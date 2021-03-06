(* coq-elpi: Coq terms as the object language of elpi                        *)
(* license: GNU Lesser General Public License Version 2.1 or later           *)
(* ------------------------------------------------------------------------- *)

DECLARE PLUGIN "elpi"

open Stdarg
open Ltac_plugin

open Pcoq
open Pcoq.Constr

module EV = Coq_elpi_vernacular

let pr_loc _ _ _ (_ : Loc.t option) = Pp.str""
ARGUMENT EXTEND elpi_loc PRINTED BY pr_loc
[ "xxxxxxxx" ] -> [ None ]
END

GEXTEND Gram GLOBAL: elpi_loc;
  elpi_loc: [[ -> Some !@loc ]];
END

VERNAC COMMAND EXTEND Elpi CLASSIFIED AS SIDEFF
| [ "Elpi" "Run" elpi_loc(loc) string(s) ] -> [ EV.exec (Option.get loc) s ]
| [ "Elpi" "Init" string_list(s) ] -> [ EV.init s ]
| [ "Elpi" "Accumulate" "File" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" "Files" string_list(s) ] -> [ EV.load_files s ]
| [ "Elpi" "Accumulate" elpi_loc(loc) string(s) ] -> [ EV.load_string (Option.get loc) s ]
| [ "Elpi" "Trace" string_opt(s) ] -> [ EV.trace s ]
| [ "Elpi" "Trace" int(start) int(stop) ] -> [ EV.trace_at start stop ]
| [ "Elpi" "Trace" "Off" ] -> [ EV.trace (Some "") ]
| [ "Elpi" "Print" "Program" string_list(s) ] -> [ EV.print s ]
END

let pr_string _ _ _ (s : string) = Pp.str s

ARGUMENT EXTEND elpi
    PRINTED BY pr_string
 [ "xxxxxxx" ] -> [ "" ]
END

let () = Coq_elpi_glob_quotation.is_coq_string := (fun x -> Genarg.(has_type x (glbwit wit_elpi)))
let () = Coq_elpi_glob_quotation.get_coq_string := (fun x -> Genarg.(out_gen (glbwit wit_elpi) x))

GEXTEND Gram
  GLOBAL: operconstr;

  operconstr: LEVEL "0"
    [ [ "lp"; ":"; id = IDENT ->
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi) id in
          CAst.make ~loc:!@loc
             (Constrexpr.CHole (None, Misctypes.IntroAnonymous, Some arg)) ] 
    | [ "lp"; ":"; s = STRING -> 
          let arg = Genarg.in_gen (Genarg.rawwit wit_elpi) s in
          CAst.make ~loc:!@loc
            (Constrexpr.CHole (None, Misctypes.IntroAnonymous, Some arg)) ] 
          ]
  ;
END


