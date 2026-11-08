-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.parse_current_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:54:14.610515+00:00
-- url     : https://prove2.me/submissions/d30cf0e2-aba1-427c-958a-09006be2e6c9

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_flag3
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_q4_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_parse4_run

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (q:ℕ) (xs:List ℕ)
 (hxs:xs.length=4) (R C:List Bool):
 (next P)^[(stream xs).length+(q+1)+1]
  (some (cfg P 3 false none [] (f::(qword q++stream xs++R)) [] C []))=
 some (cfg P 9 f (some false) [] R (qword q).reverse (pushed f (stream xs) C) []):=by
 rw [Function.iterate_add_apply,Function.iterate_one]
 simp only [Option.bind_some,flag3 P hio]
 rw [Function.iterate_add_apply]
 have hq:=q4_run P hio f (some f) q [] (stream xs++R) [] C []
 have hw:qword q++stream xs++R=unary q++false::(stream xs++R):=by simp [qword,List.append_assoc]
 rw [hw,hq]
 simp only [List.append_nil]
 have hp:=parse4_run P hio xs 0 (by simpa using hxs) f (some false) [] R (qword q).reverse C []
 have hx:xs≠[]:=by intro he;simp [he] at hxs
 simpa [hx,qword] using hp
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
