#!/usr/bin/perl
#
# f2cpp.pl - Converts Fortran 77 code to C++
#
# 2010-01-23 - Initial creation.
# 2010-02-09 - Added replacement rule for mod(a, b).
#              Fixed comment whitespace determination (I was using $#x
#              instead of length($x).
#
# Unlike f2c, the output of f2cpp.pl may or may not compile, however,
# only a small number of hand-tuned changes are typically needed.
# The resulting code is much cleaner than f2c's output, and much closer
# to the original intent of the original Fortran code.
#
# The resulting C++ code is very C-style; we basically only want C++
# for its std::complex<> type and operator overloading.
#
# Assumes single subroutine per file, and that there are
# no lines of significance above the subroutine declaration.
#
# TODOs:
# - Make the first step of conversion breaking up the input into chunks
#   delimited by subroutine boundaries. This will require full on parsing
#   of blocks.
# - Some declarations are generated incorrectly, like IZAMAX, whose array
#   argument is never an array.
# - Fix by-value argument passing of expressions (currently lets through
#   things like (-&std::conj(tau)).
# - Generate proper subroutine declarations for character arguments
#   (should be const char *, not char).
# - Determine const-ness of function declaration parameters through program
#   analysis.
# - Collapse min(a,b,c) to min(a,min(b,c)), etc. for non-binary min/max.
# - Detect instances of int(var) where var is a complex number. Replace with
#   int(var.real())
#
# END_OF_README

my %current_sub_info = (
	'in_sub', 0,
	'sub_name', '',
	'sub_args', '',
	'decl_line', 0,
);
my %FORTRAN_TYPES = (
	'logical', 'bool',
	'character', 'char',
	'integer', 'int',
	'ftnlen', 'size_t',
	'doubleprecision', 'double',
	'doublecomplex', 'std::complex<double>',
);
my %C_TYPES = (
	'bool', 'logical',
	'char', 'character',
	'int',, 'integer',
	'size_t', 'ftnlen',
	'double', 'doubleprecision',
	'std::complex<double>', 'doublecomplex',
);
my %FORTRAN_KEYWORDS = (
	"access", 1,
	"assign", 1,
	"backspace", 1,
	"blank", 1,
	"block", 1,
	"call", 1,
	"close", 1,
	"common", 1,
	"continue", 1,
	"data", 1,
	"dimension", 1,
	"direct", 1,
	"do", 1,
	"else", 1,
	"endif", 1,
	"enddo", 1,
	"end", 1,
	"entry", 1,
	"eof", 1,
	"equivalence", 1,
	"err", 1,
	"exist", 1,
	"external", 1,
	"file", 1,
	"fmt", 1,
	"form", 1,
	"format", 1,
	"formatted", 1,
	"function", 1,
	"go", 1,
	"to", 1,
	"if", 1,
	"implicit", 1,
	"include", 1,
	"inquire", 1,
	"intrinsic", 1,
	"iostat", 1,
	"logical", 1,
	"named", 1,
	"namelist", 1,
	"nextrec", 1,
	"number", 1,
	"open", 1,
	"opened", 1,
	"parameter", 1,
	"pause", 1,
	"print", 1,
	"program", 1,
	"read", 1,
	"rec", 1,
	"recl", 1,
	"return", 1,
	"rewind", 1,
	"sequential", 1,
	"status", 1,
	"stop", 1,
	"subroutine", 1,
	"then", 1,
	"type", 1,
	"unformatted", 1,
	"unit", 1,
	"write", 1,
	"save", 1,
## Fortran 90
#	"allocate", 1,
#	"allocatable", 1,
#	"case", 1,
#	"contains", 1,
#	"cycle", 1,
#	"deallocate", 1,
#	"elsewhere", 1,
#	"exit", 1,
#	"interface", 1,
#	"intent", 1,
#	"module", 1,
#	"only", 1,
#	"operator", 1,
#	"optional", 1,
#	"pointer", 1,
#	"private", 1,
#	"procedure", 1,
#	"public", 1,
#	"result", 1,
#	"recursive", 1,
#	"select", 1,
#	"sequence", 1,
#	"target", 1,
#	"use", 1,
#	"while", 1,
#	"where", 1,
## Fortran 95
#	"elemental", 1,
#	"forall", 1,
#	"pure", 1,
## Fortran 2003
#	"abstract", 1,
#	"associate", 1,
#	"class", 1,
#	"decimal", 1,
#	"decorate", 1,
#	"delegate", 1,
#	"encoding", 1,
#	"endfile", 1,
#	"enum", 1,
#	"enumerator", 1,
#	"extends", 1,
#	"extensible", 1,
#	"flush", 1,
#	"generic", 1,
#	"iomsg", 1,
#	"import", 1,
#	"move_alloc", 1,
#	"nextrec", 1,
#	"non_overridable", 1,
#	"pass", 1,
#	"pending", 1,
#	"reference", 1,
#	"round", 1,
#	"sign", 1,
#	"static", 1,
#	"typealias", 1,
## Attributes
#	"asynchronous", 1,
#	"bind", 1,
#	"protected", 1,
#	"volatile", 1,
);
use constant SCALAR => 1;
use constant VECTOR => 2;
use constant MATRIX => 3;
use constant PARAMETER => 20;
use constant UNKNOWN_TYPE => -1;
use constant SUBROUTINE => 10;
my %symbol_table = ();
my %var_dimensions = ();
my %var_types = ();
my %parameter_values = ();
my %statement_funcions = ();

sub is_comment_line{ # Determines if a line is a comment
	my $line = shift;
	return $line =~ /^[c\*\!]/i;
}
sub is_comment_or_empty_line{ # Determines if a line is a comment or is empty
	my $line = shift;
	return (($line =~ /^[c\*\!]/i) || ($line =~ /^\s*$/));
}

sub get_matching_paren_pos{
	# first char should be '('
	# returns the index of the matching ')'
	my $str = shift;
	my $i = 0;
	for(; $i < length($str); ++$i){
		last if(substr($str, $i, 1) eq '(');
	}
	++$i;
	my $paren_count = 1;
	for(; $i < length($str); ++$i){
		my $c = substr($str, $i, 1);
		if($c eq '('){
			++$paren_count;
		}elsif($c eq ')'){
			--$paren_count;
		}
		return $i if(0 == $paren_count);
	}
	return -1;
}
sub get_matching_paren_pos_backwards{
	my $str = shift;
	# last char should be ')'
	# returns the index of the matching '(' by searching backwards
	my $i = length($str) - 1;
	for(; $i >= 0; --$i){
		last if(substr($str, $i, 1) eq ')');
	}
	--$i;
	my $paren_count = 1;
	for(; $i >= 0; --$i){
		my $c = substr($str, $i, 1);
		if($c eq ')'){
			++$paren_count;
		}elsif($c eq '('){
			--$paren_count;
		}
		return $i if(0 == $paren_count);
	}
	return -1;
}
sub split_by_top_level_commas{
	# Pass in a comma delimited string
	# Splits the string into pieces separated by the commas,
	# but only top level commas; those commas that are not
	# contained within matching sets of parentheses/brackets/braces.
	my $str = shift;
	my @paren_stack;
	my $last_piece = '';
	my @ret;
	for(my $i = 0; $i < length($str); ++$i){
		my $c = substr($str, $i, 1);
		if($c eq ',' && $#paren_stack == -1){
			push(@ret, $last_piece);
			$last_piece = '';
		}else{
			$last_piece .= $c;
			if($c eq '(' || $c eq '[' || $c eq '{'){
				push(@paren_stack, $c);
			}else{
				if($c eq ')'){
					if($paren_stack[$#paren_stack] eq '('){
						pop(@paren_stack);
					}else{
						print STDERR "Unmatched $paren_stack[$#paren_stack]; got $c\n";
					}
				}elsif($c eq ']'){
					if($paren_stack[$#paren_stack] eq '['){
						pop(@paren_stack);
					}else{
						print STDERR "Unmatched $paren_stack[$#paren_stack]; got $c\n";
					}
				}elsif($c eq '}'){
					if($paren_stack[$#paren_stack] eq '{'){
						pop(@paren_stack);
					}else{
						print STDERR "Unmatched $paren_stack[$#paren_stack]; got $c\n";
					}
				}
			}
		}
	}
	push(@ret, $last_piece);
	
	return @ret;
}

sub fix_case{
	# Changes everything to lowercase (except comments)
	my $infile = shift;
	foreach $line (@$infile){
#		foreach $key (keys %FORTRAN_KEYWORDS){
#			my $key_upper = uc($key);
#			my $key_lower = lc($key);
#			$line =~ s/\b$key_upper\b/$key_lower/g;
#		}
		next if(is_comment_or_empty_line($line));
		$line =~ s/\b(\w+)\b/lc($1)/eg;
	}
}
sub replace_exponential_star_star{
	# Replaces the Fortran exponentiation operator ** with pow(...)
	my $infile = shift;
	foreach my $line (@$infile){
		next if(is_comment_or_empty_line($line));
		my $linecopy = $line;
		while($linecopy =~ /\*\*/g){
			my $starpos = pos($linecopy);
			my $before_part = substr($linecopy, 0, $starpos-2);
			my $after_part = substr($linecopy, $starpos);
			my $base = '';
			my $expo = '';
			if($before_part =~ /\)\s*$/){
				my $paren_pos = get_matching_paren_pos_backwards($before_part);
				$base = substr($before_part, $paren_pos);
				$base =~ s/^\s*\((.*)\)\s*$/\1/;
				$before_part = substr($before_part, 0, $paren_pos);
			}else{
				$before_part =~ s/(\w+)\s*$//;
				$base = $1;
			}
			if($after_part =~ /^\s*\(/){
				my $paren_pos = get_matching_paren_pos($after_part);
				$expo = substr($before_part, 0, $paren_pos+1);
				$expo =~ s/^\s*\((.*)\)\s*$/\1/;
				$after_part = substr($after_part, $paren_pos+1);
			}else{
				$after_part =~ s/^\s*(\w+)//;
				$expo = $1;
			}
			$linecopy = $before_part."pow($base, $expo)".$after_part;
			pos($linecopy) = 0;
		}
		$line = $linecopy;
	}
}
sub make_line_number_labels{
	# Makes line numbers into labels
	my $infile = shift;
	for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
		if(
			$$infile[$lineno] =~ m/^(   ([0-9]{2})\s+)(.*)/ ||
			$$infile[$lineno] =~ m/^(  ([0-9]{3})\s+)(.*)/
			){
			my $leading_str = $1;
			my $line_no = $2;
			my $remainder = $3;
			if($$infile[$lineno] =~ m/^(\s*([0-9]+)\s+)continue/i){
				my $loop_line_no = $2;
				# This could be the end of a DO ## loop, or it could just be
				# some label not associated with a loop
				# We will attempt to find the loop, if there is one
				my $found_loop = 0;
				for(my $lineno2 = 0; $lineno2 < $lineno; ++$lineno2){
					if($$infile[$lineno2] =~ /^\s*do\s+$loop_line_no\s+/i){
						$found_loop = 1;
						last;
					}
				}
				if(!$found_loop){
					$$infile[$lineno] = $current_sub_info{'sub_name'}."_L$line_no: ";
				}else{
					my @new_lines;
					push(@new_lines, $current_sub_info{'sub_name'}."_L$line_no: ");
					push(@new_lines, (' ' x length($leading_str)) . $remainder);
					splice(@$infile, $lineno, 1, @new_lines);
					++$lineno;
				}
			}else{
				my @new_lines;
				push(@new_lines, $current_sub_info{'sub_name'}."_L$line_no: ");
				push(@new_lines, (' ' x length($leading_str)) . $remainder);
				splice(@$infile, $lineno, 1, @new_lines);
				++$lineno;
			}
		}
	}
}
sub collapse_typenames{
	# Standardizes a bunch of various Fortran types
	my $infile = shift;
	foreach(@$infile){
		s/\bdouble precision\b/doubleprecision/gi;
		s/\bdouble complex\b/doublecomplex/gi;
		s/\bcomplex\*16\b/doublecomplex/gi;
		s/\breal\*8\b/doubleprecision/gi;
	}
}
sub replace_binary_comparison_ops{
	# Replaces the .OP. operators with standard C comparison operators
	my $infile = shift;
	foreach(@$infile){
		s/\.gt\./ > /gi;
		s/\.ge\./ >= /gi;
		s/\.lt\./ < /gi;
		s/\.le\./ <= /gi;
		s/\.eq\./ == /gi;
		s/\.ne\./ != /gi;
		s/\.not\./ !/gi;
		s/\.and\./ && /gi;
		s/\.or\./ || /gi;
		s/\.true\./true/gi;
		s/\.false\./false/gi;
	}
}
sub grab_parameter_values{
	# Records Fortran PARAMETERs
	my $infile = shift;
	foreach $line (@$infile){
		if($line =~ m/^\s*parameter\s*\((.*)\)\s*$/i){
			my $param_list = $1;
			while(length($param_list) > 0){
				$param_list =~ s/^\s*(\w+)//;
				my $param_name = $1;
				$param_list =~ s/^\s*(=)\s*//;
				if($1){
					my $param_val = '';
					if($param_list =~ s/^\(([^\),]+),([^\),]+)\),?//){
						my $real_part = $1;
						my $imag_part = $2;
						$real_part =~ s/^\s*(.*?)\s*$/\1/;
						$imag_part =~ s/^\s*(.*?)\s*$/\1/;
						$param_val = "std::complex<double>($real_part, $imag_part)";
					}else{
						$param_list =~ s/^([^,]+),?//;
						$param_val = $1;
					}
					$parameter_values{$param_name} = $param_val;
					$param_list =~ s/^\s*//;
					#print STDERR $param_name, " ", $param_val, "\n";
				}
			}
#			my @param_list = split(/,/, $1);
#			foreach $param (@param_list){
#				$param =~ s/ //g;
#				my ($param_name, $param_val) = split(/=/, $param);
#				$symbol_table{$param_name} = PARAMETER;
#				$param_val =~ s/([0-9])d(-?[0-9])/\1e\2/i;
#				if($param_val eq '0e0'){ $param_val = '0.0'; }
#				elsif($param_val eq '1e0'){ $param_val = '1.0'; }
#				$parameter_values{$param_name} = $param_val;
#				#print "Found parameter $param_name with value $param_val\n";
#			}
			$line =~ s/^(\s*)/\1\/\/ /;
		}
	}
}
sub rewrite_character_vardecls{
	# Rewrites variables declared as CHARACTER NAME*LEN
	# into: character name[len]
	my $infile = shift;
	for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
		if($$infile[$lineno] =~ m/^(\s*)character\s+(.*)\s*$/){
			my $leading_whitespace = $1;
			my @new_lines;
			foreach $strname (split(/,\s/, $2)){
				my $strlen = 0;
				($strname,$strlen) = split(/\*/, $strname);
				++$strlen;
				push(@new_lines, $leading_whitespace."character $strname\[$strlen\]");
			}
			splice(@$infile, $lineno, 1, @new_lines);
			$lineno += $#new_lines;
		}
	}
}
sub expand_external_statements{
	# Places each EXTERNAL declaration on its own line
	my $infile = shift;
	for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
		if($$infile[$lineno] =~ m/^(\s*)external\s+(.*)\s*$/){
			my $leading_whitespace = $1;
			my @new_lines;
			foreach $proc (split(/,\s/, $2)){
				push(@new_lines, $leading_whitespace."external $proc");
			}
			splice(@$infile, $lineno, 1, @new_lines);
			$lineno += $#new_lines;
		}
	}
}
sub set_parameters{
	# Applies the recorded PARAMETER values and rewrites the declarations to be const
	my $infile = shift;
	foreach $line (@$infile){
		foreach $ctype (keys %C_TYPES){
			if($line =~ m/^(\s*)$ctype\s+(\w+)\s*$/){
				my $leading_whitespace = $1;
				my $varname = $2;
				#print STDERR "$varname\n";
				if($parameter_values{$varname}){
					$line = $leading_whitespace . 'const ' . $ctype . ' ' . $varname . ' = ' . $parameter_values{$varname};
				}
			}
		}
	}
}

sub replace_types{
	# Performs replacement of types from Fortran into C++ types
	my $infile = shift;
	foreach(@$infile){
		s/\bdoubleprecision\b/double/gi;
		s/\blogical\b/bool/gi;
		s/\binteger\b/int/gi;
		s/\bcharacter\b/char/gi;
		s/\bdoublecomplex\b/std::complex<double>/gi;
		s/\bimplicit none\b//gi;
	}
}

sub replace_simple_intrinsics{
	# Performs replacement of several simple intrinsic functions
	my $infile = shift;
	foreach(@$infile){
		s/\bdcmplx\b/std::complex<double>/gi;
		s/\bdconjg\b/std::conj/gi;
		s/\bdble\b/std::real/gi;
		s/\bdimag\b/std::imag/gi;
		s/([^\:])?\babs\b/\1std::abs/gi; # all abs go to std::abs
		# Replace mod(a, b) with (a % b)
		s/\bmod\s*\(\s*(\w+)\s*,\s*(\w+)\s*\)/(\1 % \2)/gi;
	}
}

sub format_loops{
	# Rewrites loops and loop delimiters
	my $infile = shift;
	foreach $line (@$infile){
		if(is_comment_or_empty_line($line)){ next; }
		$line =~ s/\bdo\swhile(.*)$/while\1\{/i;
		$line =~ s/\bthen\b/\{/i;
		$line =~ s/\bendif\b/\}/i;
		$line =~ s/\bend if\b/\}/i;
		$line =~ s/\benddo\b/\}/i;
		$line =~ s/(\s*)else(\s*)/\1\}else\{\2/i;
		$line =~ s/\}else\{\s+if\s*\(/\1\}else if\(/i; # fix errors generated by prev line
		$line =~ s/\bcontinue\b/\}/i;
		#$line =~ s/\bend\b/\}/i; # we need to process end specially, do deal with end of subroutines
		$line =~ s/\bexternal\b/extern/i;

		my $linecopy = $line;
		if($linecopy =~ /(\s*)do\s+(([0-9]+)\s+)?(\w+)\s*=/g){
			my $leading_whitespace = $1;
			my $continue_line = $3;
			my $loop_var = $4;
			my $endpos = pos($linecopy);
			my @loop_limits = split_by_top_level_commas(substr($linecopy, $endpos));
			if($#loop_limits == 1){ # start, end
				$loop_limits[0] =~ s/^\s*(.*?)\s*$/\1/;
				$loop_limits[1] =~ s/^\s*(.*?)\s*$/\1/;
				$line = $leading_whitespace . "for($loop_var = $loop_limits[0]; $loop_var <= $loop_limits[1]; ++$loop_var){";
			}elsif($#loop_limits == 2){ # start, end, inc
				$loop_limits[0] =~ s/^\s*(.*?)\s*$/\1/;
				$loop_limits[1] =~ s/^\s*(.*?)\s*$/\1/;
				$loop_limits[2] =~ s/^\s*(.*?)\s*$/\1/;
				my $incint = int($loop_limits[2]);
				my $incop = '+=';
				if($inc.'' eq $incint){
					if($incint < 0){
						$line = $leading_whitespace . "for($loop_var = $loop_limits[0]; $loop_var >= $loop_limits[1]; $loop_var -= $loop_limits[2]){";
					}else{
						$line = $leading_whitespace . "for($loop_var = $loop_limits[0]; $loop_var <= $loop_limits[1]; $loop_var += $loop_limits[2]c){";
					}
				}else{
					$line = $leading_whitespace . "for($loop_var = $loop_limits[0]; (($loop_limits[2] < 0) ? ($loop_var >= $loop_limits[1]) : ($loop_var <= $loop_limits[1])); $loop_var += $loop_limits[2]){";
				}
			}
		}
	}
}

sub infer_types_correct_arrays{
	# This is the main function which figures out what type each variable is.
	# This function also records information about the current (only) subroutine.
	my $infile = shift;
	for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
		my $line = $$infile[$lineno];
		next if(is_comment_or_empty_line($line));
		if($current_sub_info{'in_sub'}){
			# If we are within a subroutine, then try to rewrite all non-scalar variables with C-style indexing
			if($line =~ /^(\s*)end\s*$/i){
				# We hit the end of the subroutine, we have enough info to rewrite the subroutine declaration at the top.
				$$infile[$lineno] = "$1}";
				$current_sub_info{'in_sub'} = 0;
				# Fix up the declaration
				my @sub_args = split(/\s/, $current_sub_info{'sub_args'});
				foreach $arg (@sub_args){
					if($symbol_table{$arg} == MATRIX || $symbol_table{$arg} == VECTOR){
						$arg = "$var_types{$arg} *$arg";
					}else{
						$arg = "$var_types{$arg} $arg";
					}
				}
				$$infile[$current_sub_info{'decl_line'}] = 'void ' . $current_sub_info{'sub_name'} . '(' . join(', ', @sub_args) . "){";
				# add in a using namespace std (semicolon added later)
				splice(@$infile, $current_sub_info{'decl_line'}+1, 0, ("\tusing namespace std"));
				next;
			}
			my $found_decl = 0;
			KEYS: foreach $key (keys %FORTRAN_TYPES){
				if($line =~ m/(\s*)$key\b/i){
					# We found a variable declaration, record its type and dimensions, if any.
					my $leading_whitespace = $1;
					my @new_decls = ();
					$line =~ m/\b$key\s+(.+)$/i;
					my $list_of_varnames = $1;
					# First substitute commas for dimension separators for something else so we can split the list
					$list_of_varnames =~ s/\(([^\)]+),([^\)]+)\)/(\1|\2)/g;
					@varnames = split(/,/, $list_of_varnames);
					foreach $vardecl (@varnames){
						$vardecl =~ s/ //g;
						$vardecl =~ m/^(\w+)(\s*\((.*)\))?$/;
						my $varname = $1;
						my $dimstuff = $3;
						my $stripped_varname = $varname;
						if($2){
							$dimstuff =~ m/(.*?)(\|(.*))?$/;
							if($2){
								my $dim1 = $1; $dim1 =~ s/ //g;
								my $dim2 = $3; $dim2 =~ s/ //g;
								$symbol_table{$varname} = MATRIX;
								$var_dimensions{$varname} = "$dim1 $dim2";
								#print "$varname is a matrix, dims $dim1 $dim2\n";
							}else{
								my $dim1 = $1; $dim1 =~ s/ //g;
								$symbol_table{$varname} = VECTOR;
								$var_dimensions{$varname} = "$dim1";
								#print STDERR "$varname is a vector, length $dim1\n";
							}
						}else{
							$stripped_varname =~ s/\[[0-9]*\]$//;
							$symbol_table{$stripped_varname} = SCALAR;
							#print "$varname is a scalar\n";
						}
						# Add the type info
						$var_types{$stripped_varname} = $key;
						# Check to see if $varname is a subroutine argument
						# if it is, don't add it to the new decl list
						unless($current_sub_info{'sub_args'} =~ /\b$stripped_varname\b/){
							my $var_dim = 0;
							if($symbol_table{$varname} == VECTOR){
								if($var_dimensions{$varname} =~ /^[0-9]+$/){
									$var_dim = $var_dimensions{$varname};
								}
							}elsif($symbol_table{$varname} == MATRIX){
								if($var_dimensions{$varname} =~ /^([0-9]+)\s+([0-9]+)$/){
									$var_dim = $1 * $2;
								}
							}
							if($var_dim > 0){
								push(@new_decls, "$leading_whitespace$key $varname\[$var_dim]");
							}else{
								push(@new_decls, "$leading_whitespace$key $varname");
							}
						}
					}
					splice(@$infile, $lineno, 1, @new_decls);
					$lineno += $#new_decls;
					$found_decl = 1;
					last KEYS;
				}
			}
			unless($found_decl){
				unless(is_comment_or_empty_line($line)){
					# We get here if the current line is not a variable declaration.
					# We try to replace all non-scalar variables by a C-style indexing subscript
					my $add_amps = 0;
					my $ident = '';
					my $last_ident = '';
					my $ident_pos = 0;
					if($line =~ /\s*call\s*\w+/i){
						$add_amps = 1;
					}
					my $prev_ident = '';
					my @paren_stack;
					
					my $func_call_level = $#paren_stack;
					my $in_func_call = 0;
					for(my $charpos = 0; $charpos < length($$infile[$lineno]); ++$charpos){
						my $c = substr($$infile[$lineno], $charpos, 1);
						$ident = '';
						if($c =~ /\w/){
							if($last_ident eq ''){
								$ident_pos = $charpos;
							}
							$last_ident .= $c;
						}else{
							if($c eq '(' || $c eq '[' || $c eq '{'){
								push(@paren_stack, $c);
							}
# Forget about checking for this; we should not have messed it up.
# Infact, we replace array subscripts () with [], so we really screw
# up the matching pretty badly, enough that it's hard to keep it straight here.
#							elsif($c eq ')'){
#								if($paren_stack[$#paren_stack] eq '('){
#									pop(@paren_stack);
#								}else{
#									print "// Unmatched $paren_stack[$#paren_stack] on line $lineno, got $c\n";
#								}
#							}elsif($c eq ']'){
#								if($paren_stack[$#paren_stack] eq '('){ # Note that this should be a round paren; it was replaced with square brackets
#									pop(@paren_stack);
#								}else{
#									print "// Unmatched $paren_stack[$#paren_stack] on line $lineno, got $c\n";
#									print substr($$infile[$lineno], 0, $charpos), "\n";
#								}
#							}elsif($c eq '}'){
#								if($paren_stack[$#paren_stack] eq '{'){
#									pop(@paren_stack);
#								}else{
#									print "// Unmatched $paren_stack[$#paren_stack] on line $lineno, got $c\n";
#								}
#							}
							if($#paren_stack < $func_call_level){
								$in_func_call = 0;
								$add_amps = 0;
							}
							$ident = $last_ident;
							$last_ident = '';
							# If we are entering a function call
							if($symbol_table{$ident} == SCALAR){
								if(substr($$infile[$lineno], $charpos) =~ /^\s*\(/){
									$func_call_level = $#paren_stack+1;
									$in_func_call = 1;
									$add_amps = 1;
								}
							}
						}
						if($ident eq ''){ next; }
						$ident_pos += length($ident);
						next if($FORTRAN_KEYWORDS{$ident} || ($ident =~ /[0-9]+/));
						if(1){
							#print "Found identifier $ident\n";
							if($symbol_table{$ident} == VECTOR){
								#print "Found vector $ident, $ident_pos\n";
								#print substr($line, $ident_pos);
								if(substr($$infile[$lineno],$ident_pos,1) eq '('){
									my $line_before = substr($$infile[$lineno], 0, $ident_pos);
									if($add_amps){
										$line_before = substr($line_before, 0, $ident_pos-length($ident)) . '&' . $ident;
									}
									my $line_after = substr($$infile[$lineno], $ident_pos);
									$line_after =~ s/\(([^\)]+)\)/[(\1)-1]/;
									$$infile[$lineno] = $line_before.$line_after;
								}
							}elsif($symbol_table{$ident} == MATRIX){

								#print "Found matrix $ident, $ident_pos\n";
								#print substr($line, $ident_pos);
								if(substr($$infile[$lineno],$ident_pos,1) eq '('){
									my $line_before = substr($$infile[$lineno], 0, $ident_pos);
									if($add_amps){
										$line_before = substr($line_before, 0, $ident_pos-length($ident)) . '&' . $ident;
									}
									my $line_after = substr($$infile[$lineno], $ident_pos);
									my $lda = $var_dimensions{$ident};
									$lda =~ s/^(\S+).*$/\1/;
									# BUG: this converts things like a(min(b,c),d) incorrectly:
									# $line_after =~ s/\(([^\),]+),([^\)]+)\)/[((\1)-1)+((\2)-1)*($lda)]/;
									my $paren_pos = get_matching_paren_pos($line_after);
									my $index_str = substr($line_after, 1, $paren_pos-1);
									my $old_len = length($index_str);
									#print STDERR "$index_str\n";
									$line_after = substr($line_after, $paren_pos+1);
									my @indices = split_by_top_level_commas($index_str);
									#print STDERR "$indices[0] | $indices[1]\n";
									$index_str = "\[(($indices[0])-1)+(($indices[1])-1)*($lda)\]";
									my $new_len = length($index_str);
									$$infile[$lineno] = $line_before.$index_str.$line_after;

									$charpos += $new_len;
								}
							}
							#print "$symbol_table{$ident}\n";
						}
						$prev_ident = $ident;
						$ident = '';
					}
				}
			}
		}else{
			# We were not in a subroutine, so try to detect the start of one
			if($line =~ /^\s*subroutine\b/i){
				$current_sub_info{'in_sub'} = 1;
				%symbol_table = {};
				%var_dimensions = {};
				%var_types = {};
				# Grab all of the argument names
				$line =~ m/^\s*subroutine\s+(\w+)\s*\(\s*(.*)\s*\)\s*$/i;
				$current_sub_info{'sub_name'} = $1;
				$symbol_table{$1} = SUBROUTINE;
				my @args = split(/,\s/, $2);
				$current_sub_info{'sub_args'} = join(' ', @args);
				$current_sub_info{'decl_line'} = $lineno;
				foreach $arg (@args){
					$symbol_table{$arg} = UNKNOWN_TYPE;
				}
			}
		}
	}
}

sub format_comments{
	# Formats Fortran comments into C99-style single line comments
	# We try to find the local indentation level and match the comment indentation to that.
	my $infile = shift;
	for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
		if(is_comment_or_empty_line($$infile[$lineno])){
			my $prev_noncomment_lineno = $lineno;
			my $next_noncomment_lineno = $lineno;
			my $have_prev = 0;
			my $have_next = 0;
			while($prev_noncomment_lineno > 0){
				--$prev_noncomment_lineno;
				unless($$infile[$prev_noncomment_lineno] =~ /^\s*$/ || $$infile[$prev_noncomment_lineno] =~ /^\s*\/\//){
					$have_prev = 1;
					last;
				}
			}
			while($next_noncomment_lineno < $#$infile){
				++$next_noncomment_lineno;
				if(!is_comment_or_empty_line($$infile[$next_noncomment_lineno])){
					$have_next = 1;
					last;
				}
			}
			#print "$lineno  : $have_prev $have_next $prev_noncomment_lineno $next_noncomment_lineno\n";
			if($have_prev){
				if($have_next){
					$$infile[$prev_noncomment_lineno] =~ /(\s*)/;
					my $leading_whitespace1 = $1;
					$leading_whitespace1 =~ s/\t/    /g;
					$$infile[$next_noncomment_lineno] =~ /(\s*)/;
					my $leading_whitespace2 = $1;
					$leading_whitespace2 =~ s/\t/    /g;
					my $leading_whitespace = $leading_whitespace1;
					if(length($leading_whitespace2) > length($leading_whitespace1)){
						$leading_whitespace = $leading_whitespace2;
					}
					#print "'$leading_whitespace'", length($leading_whitespace), "\n";
					if(length($leading_whitespace) < 3){
						$leading_whitespace = '// ';
					}else{
						$leading_whitespace .= '// ';
					}
					$$infile[$lineno] =~ s/.(\s*)/$leading_whitespace/;
				}else{
					$$infile[$prev_noncomment_lineno] =~ /(\s*)/;
					my $leading_whitespace = $1;
					$leading_whitespace =~ s/\t/    /g;
					if(length($leading_whitespace) < 3){
						$leading_whitespace = '// ';
					}else{
						$leading_whitespace =~ s/   $/\/\/ /;
					}
					$$infile[$lineno] =~ s/.(\s*)/$leading_whitespace/;
				}
			}elsif($have_next){
				$$infile[$next_noncomment_lineno] =~ /(\s*)/;
				my $leading_whitespace = $1;
				$leading_whitespace =~ s/\t/    /g;
				if(length($leading_whitespace) < 3){
					$leading_whitespace = '// ';
				}else{
					$leading_whitespace =~ s/   $/\/\/ /;
				}
				$$infile[$lineno] =~ s/.(\s*)/$leading_whitespace/;
			}else{
				$$infile[$lineno] =~ s/./\/\//;
			}
		}
	}
};

sub add_semicolons{
	# Places semicolons at the ends of lines which need them
	my $infile = shift;
	foreach my $line (@$infile){
		if($line =~ /^\s*$/){ next; }
		if($line =~ /\{\s*$/ || $line =~ /\}\s*$/){
			next;
		}
		if($line =~ /^\s*\/\//){ next; }
		$line .= ';';
	}
}

sub simplify_subscripts{
	# Performs some simple subscript simplification; the rewrite from Fortran to C subscripts generates many extra parentheses.
	my $infile = shift;
	foreach my $line (@$infile){
		my $linecopy = $line;
		$line = '';
		while($linecopy =~ /(.*?)(\[[^\]]+\])(.*)/g){
			my $before = $1;
			my $subscript = $2;
			my $after = $3;
			
			# Just keep doing passes instead of anything intelligent
			for(my $count = 0; $count < 10; ++$count){
				$subscript =~ s/\(([0-9]+)\)/\1/g;
				$subscript =~ s/\(\s*(\w+)\s*\)/\1/g;
				$subscript =~ s/\(1\-1\)/0/g;
				$subscript =~ s/\(1\+1\)/2/g;
				$subscript =~ s/\(2\-1\)/1/g;
				$subscript =~ s/\(\((\w+)\-1\)+1\)/(\1)/g;
				$subscript =~ s/\(\((\w+)\+1\)-1\)/(\1)/g;
				
				$subscript =~ s/\(\(([^\(\)]+)\+1\)\-1\)/(\1)/g;
				$subscript =~ s/\(\(([^\(\)]+)\-1\)\+1\)/(\1)/g;
				
				$subscript =~ s/\(\(([^\(\)]+)\-(\w+)\)\-(\w+)\)/((\1)-((\2)+(\3)))/g;
				$subscript =~ s/\(\(([^\(\)]+)\+(\w+)\)\+(\w+)\)/((\1)+((\2)+(\3)))/g;
			}
			#print "$linecopy\n";
			$linecopy = $after;
			#print "$linecopy\n";
			#print "$line\n";
			$line .= $before.$subscript;
			#print "$line\n-------\n";
			pos($linecopy) = 0;
		}
		$line .= $linecopy;
	}
}

sub detect_loop_vars{
	# We try to detect loop/index variables as a hint for human post-processing.
	my $infile = shift;
	my %loop_vars;
	for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
		my $line = $$infile[$lineno];
		if($line =~ /for\((\w+) \= /){
			$loop_vars{$1} = 1;
			#print "$1 - $line\n";
		}
	}
	my %bracket_vars;
	for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
		my $line = $$infile[$lineno];
		my @bracket_contents_to_process;
		while($line =~ /\[([^\]]+)\]/g){
			push(@bracket_contents_to_process, $1);
		}
		foreach $bracket_contents (@bracket_contents_to_process){
			while($bracket_contents =~ /(\w+)/g){
				my $possible_symbol = $1;
				if(!($possible_symbol =~ /^[0-9]+$/)){
					$bracket_vars{$possible_symbol} = 1;
				}
			}
		}
	}
	# We found all the variables in brackets, but we should throw out all variables
	# which are also involved in matrix/vector dimensions.
	my %dim_vars;
	foreach $key (keys(%symbol_table)){
		if($symbol_table{$key} == MATRIX){
			foreach $dimstuff (split(/\s/, $var_dimensions{$key})){
				while($dimstuff =~ /(\w+)/g){
					my $possible_symbol = $1;
					if(!($possible_symbol =~ /^[0-9]+$/)){
						$dim_vars{$possible_symbol} = 1;
					}
				}
			}
		}elsif($symbol_table{$key} == VECTOR){
			foreach $dimstuff (split(/\s/, $var_dimensions{$key})){
				while($dimstuff =~ /(\w+)/g){
					my $possible_symbol = $1;
					if(!($possible_symbol =~ /^[0-9]+$/)){
						$dim_vars{$possible_symbol} = 1;
					}
				}
			}
		}
	}
	foreach $key (keys(%dim_vars)){
		delete $bracket_vars{$key};
	}
	print "// Detected the following indicial variables: " . join(', ', keys(%bracket_vars)) . "\n";
}
sub emit_c_decl{
	# Prints out the C function declarations for all referenced functions.
	my $sub_name = shift; # sub_name could also be a function name
	my $sub_args = shift;
	my $ret_type = shift;
	#print "emit_c_decl: $ret_type $sub_name($sub_args)\n";
	
	my $is_sub_arg = 0;
	if($current_sub_info{'sub_args'} =~ /\b$sub_name\b/){
		$is_sub_arg = 1;
	}
	
	my @args;
	my $cur_arg = '';
	my @paren_stack;
	for(my $i = 0; $i < length($sub_args); $i++){
		my $c = substr($sub_args, $i, 1);
		if($c eq ',' && $#paren_stack == -1){
			$cur_arg =~ s/^\s*(.*)\s*$/\1/;
			push(@args, $cur_arg);
			#print $cur_arg, "\n";
			$cur_arg = '';
		}else{
			if($c eq '(' || $c eq '[' || $c eq '{'){
				push(@paren_stack, $c);
			}elsif($c eq ')'){
				if($paren_stack[$#paren_stack] eq '('){
					pop(@paren_stack);
				}else{
					print "// Mismatched '(' in call to $sub_name\n";
				}
			}elsif($c eq ']'){
				if($paren_stack[$#paren_stack] eq '['){
					pop(@paren_stack);
				}else{
					print "// Mismatched ']' in call to $sub_name\n";
				}
			}elsif($c eq '}'){
				if($paren_stack[$#paren_stack] eq '{'){
					pop(@paren_stack);
				}else{
					print "// Mismatched '{' in call to $sub_name\n";
				}
			}
			$cur_arg .= $c;
		}
	}
	if($#paren_stack != -1){
		print "// Mismatched '$paren_stack[$#paren_stack]' in call to $sub_name\n";
	}
	$cur_arg =~ s/^\s*(.*)\s*$/\1/;
	push(@args, $cur_arg);
	#print $cur_arg, "\n";
	
	# At this point, all the arguments for the call are in @args
	my @arg_types;
	# For each arg, find symbols and their types.
	# We assume the first symbol in our table well define the type
	foreach $arg (@args){
		if($arg =~ /^\s*\".*\"\s*$/){
			push(@arg_types, 'const char *');
			next;
		}
		if($arg =~ /^\s*[0-9]+\s*$/){
			push(@arg_types, 'size_t');
			next;
		}
		if($arg =~ /^\s*true\s*$/i || $arg =~ /^\s*false\s*$/i){
			push(@arg_types, 'bool');
			next;
		}
		my $ast = '';
		my $const = '';
		if($arg =~ /^\s*\&/){
			$const = 'const ';
			$ast = '*';
		}
		my $found = 0;
		while($arg =~ /(\w+)(\s*\[)?/g){
			my $cur_sym = $1;
			my $is_subscripted = 0;
			if($2){ $is_subscripted = 1; }
			next if($cur_sym =~ /^[0-9]*$/);
			if(my $stype = $symbol_table{$cur_sym}){
				if($var_types{$cur_sym} eq 'character'){
					push(@arg_types, "const char *");
				}else{
					if(!$is_subscripted && ($stype == MATRIX || $stype == VECTOR && $ast eq '')){
						$const = 'const ';
						$ast = '*';
					}
					push(@arg_types, $const.$FORTRAN_TYPES{$var_types{$cur_sym}}.$ast);
				}
				$found = 1;
				last;
			}
		}
		if($found == 0){
			push(@arg_types, $const.'unknown_type'.$ast);
		}
	}

	if($is_sub_arg){
		return "$ret_type (*$sub_name)(" . join(', ', @arg_types) . ")";
	}else{
		if($statement_functions{$sub_name}){
			my $cur_line = "static inline $ret_type $sub_name(";
			my $equal_pos = index($statement_functions{$sub_name}, '=');
			my $body = substr($statement_functions{$sub_name}, $equal_pos+1);
			$body =~ s/^\s*(.*?)\s*$/\1/;
			
			my $bodylist = [$body];
			replace_simple_intrinsics($bodylist);
			$body = $$bodylist[0];
			
			my @arglist = split(/,/, substr($statement_functions{$sub_name}, 0, $equal_pos));
			if($#arg_types == $#arglist){
				for(my $i = 0; $i <= $#arglist; ++$i){
					$arglist[$i] =~ s/^\s*(.*?)\s*$/\1/;
					$arg_types[$i] .= " $arglist[$i]";
				}
				$cur_line .= join(', ', @arg_types) . "){ return $body; }";
				print $cur_line, "\n";
			}else{
				print "// Argument number mismatch in call to $sub_name\n";
				return '';
			}
		}else{
			print "$ret_type $sub_name(" . join(', ', @arg_types) . ");\n";
			return '';
		}
	}
};
sub get_statement_functions{
	# Finds statement function declarations and generates a function for them
	my $infile = shift;
	foreach my $line (@$infile){
		if($line =~ /\b(\w+)\s*\(/g){ # only need to find the first one in the line; it must be first
			my $start_paren_pos = pos($line)-1;
			my $possible_sfunc_name = $1;
			if($symbol_table{$possible_sfunc_name} == SCALAR){
				my $end_paren_pos = get_matching_paren_pos(substr($line, $start_paren_pos));
				next if($end_paren_pos == -1);
				my $possible_arg_list = substr($line, $start_paren_pos+1, $end_paren_pos-1);
				if(substr($line, $start_paren_pos+$end_paren_pos+1) =~ /\s*\=/){
					# Right after the parenthesized list is an equal sign, so this is a statement function
					$statement_functions{$possible_sfunc_name} = $possible_arg_list . substr($line, $start_paren_pos+$end_paren_pos+1);
					# Stored as:
					# arglist = body
					#print STDERR $statement_functions{$possible_sfunc_name}, "\n";
					$line =~ s/^(\s*)/\1\/\/ /;
				}
			}
		}
		pos($line) = 0;
	}
}
sub fixup_calls{
	# Rewrites all calls to subroutines and functions, records the function parameter lists for figuring out the declarations.
	my $infile = shift;
	my %sub_names = ();
	foreach $line (@$infile){
		if($line =~ /\s*call\s+(\w+)\s*\(\s*(.*?)\s*\)\s*$/i){
			my $sub_name = $1;
			my $arglist = $2;
			$line =~ s/\'/\"/g;
			$arglist =~ s/\'/\"/g;
			$line =~ s/(\s*)call\s+/\1/i;
			# A call statement
			#print STDERR "$line\n";
			$sub_names{$sub_name} = $arglist;
		}
	}
	my %func_names = ();
	foreach $line (@$infile){
		my $found = 0;
		while($line =~ /\b(\w+)(\s*\()/g){
			if($symbol_table{$1} == SCALAR){
				if($var_types{$1} eq 'character'){
					# this is not a function, this is a substring
				}else{
					# A function
					my $func_name = $1;
					# print "func: $1\n";
					my $paren_number = 1;
					my $func_call = '';
					# Grab until the end parenthesis
					my $i = pos($line);
					for(; $i < length($line); ++$i){
						my $c = substr($line, $i, 1);
						if($c eq '('){
							$paren_number++;
						}elsif($c eq ')'){
							$paren_number--;
						}
						if($paren_number == 0){
							last;
						}
						$func_call .= $c;
					}
					pos($line) = $i;
					#print "$func_call\n";
					$func_call =~ s/\'/\"/g;
					$func_names{$func_name} = $func_call;
					$found = 1;
				}
			}
		}
		if($found){
			$line =~ s/\'/\"/g;
		}
	}
	# delete the variable declararations of the function names
	for(my $i = 0; $i <= $#$infile; $i++){
		foreach $ctype (keys %C_TYPES){
			if($$infile[$i] =~ m/^(\s*)$ctype\s+(\w+)\s*$/){
				my $varname = $2;
				if($func_names{$varname}){
					splice(@$infile, $i, 1);
					--$i;
					last;
				}
			}
		}
	}
	# Now figure out the prototypes for the subs and functions
	# The values of both sub_names and func_names are the list of
	# comma separated arguments. Note that they may have nested commas, which
	# we ignore
	my %processed_names;
	foreach $sub_name (keys(%sub_names)){
		next if($processed_names{$sub_name});
		$processed_names{$sub_name} = 1;
		my $decl = emit_c_decl($sub_name, $sub_names{$sub_name}, 'void');
		#print STDERR "$sub_name $decl\n";
		# Only subs can be arguments to subroutines (I think)
		if($decl ne ''){
			# We need to replace the subroutine's argument with this
			$$infile[$current_sub_info{'decl_line'}] =~ s/\b$sub_name\b/$decl/;
		}
		# We also need to remove the extern line for this
		for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
			if($$infile[$lineno] =~ /^\s*extern\s+$sub_name/){
				splice(@$infile, $lineno, 1);
				--$lineno;
			}
		}
	}
	foreach $func_name (keys(%func_names)){
		#print $func_names{$func_name}, "\n";
		next if($processed_names{$func_name});
		$processed_names{$func_name} = 1;
		my $decl = emit_c_decl($func_name, $func_names{$func_name}, $FORTRAN_TYPES{$var_types{$func_name}});
		
		# We also need to remove the extern line for this
		for(my $lineno = 0; $lineno <= $#$infile; ++$lineno){
			if($$infile[$lineno] =~ /^\s*extern\s+$sub_name/){
				splice(@$infile, $lineno, 1);
				--$lineno;
			}
		}
	}
}
sub remove_intrinsics{ # remove the intrisic declarations
	# This deletes all declarations of INTRINSIC functions
	my $infile = shift;
	for(my $i = 0; $i <= $#$infile; $i++){
		if($$infile[$i] =~ /^\s*intrinsic\s+/i){
			splice(@$infile, $i, 1);
			--$i;
		}
	}
}
sub fix_numeric_constants{
	# Rewrites Fortran floating point constants into C-style numbers.
	my $infile = shift;
	for $line (@$infile){
		$line =~ s/\b([0-9]+(\.([0-9]+)?)?)d([-+]?[0-9]+)\b/\1e\4/gi;
		#$line =~ s/\b0.0e.0\b/0.0/g;
		#$line =~ s/\b1.0e.0\b/1.0/g;
		#$line =~ s/\b0e0\b/0.0/g;
		#$line =~ s/\b1e0\b/1.0/g;
	}
}
sub fix_gotos{
	# Rewrites Fortran's GO TO into goto's with the label format generated by make_line_number_labels
	my $infile = shift;
	for $line (@$infile){
		$line =~ s/go\s+to\s([0-9]+)/goto $current_sub_info{'sub_name'}_L\1/i;
	}
}
sub prettify{
	# Applies custom C formatting rules for whitespace removal
	my $infile = shift;
	for $line (@$infile){
		$line =~ s/\bif\s+\(/if(/;
		$line =~ s/\)\s+\{\s*$/)\{/;
	}
}
sub emit_header{
	# Prints out the standard C++ headers needed
	print "#define NOMINMAX\n";
	print "#include <cstddef>\n";
	print "#include <algorithm>\n";
	print "#include <cmath>\n";
	print "#include <complex>\n";
}
sub main{
	my @infile;
	my $infilename = shift;
	open(FP, "<$infilename") or die "Could not open $infilename";
	while(<FP>){
		chomp;
		s/\t/        /g;
		push(@infile, $_);
	}
	close(FP);

	# Join continuation lines
	my $prev_line = 0;
	for(my $i = 1; $i <= $#infile; ++$i){
		#print "~~~ " . $infile[$i] . "\n";
		if($infile[$i] =~ /^\s*\$/){
			$infile[$i] =~ s/^\s*\$\s*//;
			$infile[$prev_line] .= ' ' . $infile[$i];
			# remove line $i from $infile
			#print "Removing line " . $infile[$i]." : prev_line = $prev_line, i = $i\n";
			splice(@infile, $i, 1);
			#print "Line i is " . $infile[$i] . "\n";
			#print "Prev line i is " . $infile[$prev_line] . "\n\n";
			--$i;
			# $prev_line is still the same, and $i is still the same
		}else{
			#print "skip\n";
			$prev_line = $i;
		}
	}

	# We proceed with multiple passes through the file, slowly converting it a little at a time.
	emit_header();

	fix_case(\@infile);
	collapse_typenames(\@infile);
	rewrite_character_vardecls(\@infile);
	grab_parameter_values(\@infile);
	expand_external_statements(\@infile);
	remove_intrinsics(\@infile);
	replace_binary_comparison_ops(\@infile);
	replace_exponential_star_star(\@infile);
	infer_types_correct_arrays(\@infile); # fills in current_sub_info
	make_line_number_labels(\@infile);
	fix_gotos(\@infile);
	simplify_subscripts(\@infile);
	format_loops(\@infile);
	detect_loop_vars(\@infile);
	replace_types(\@infile);
	format_comments(\@infile);
	set_parameters(\@infile);
	get_statement_functions(\@infile);
	fixup_calls(\@infile);
	replace_simple_intrinsics(\@infile);
	add_semicolons(\@infile);
	fix_numeric_constants(\@infile);
	prettify(\@infile);
	
	print "// Declarations need repairing; reference/pointers need to be replaced.\n\n";
	foreach(@infile){
		print "$_\n";
	}
}

main(@ARGV);

