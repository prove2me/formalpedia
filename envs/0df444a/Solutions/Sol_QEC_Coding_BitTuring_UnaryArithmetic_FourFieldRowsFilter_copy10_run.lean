-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.copy10_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:11:32.715201+00:00
-- url     : https://prove2.me/submissions/c1b91d8e-901e-4536-bafa-fd8209747431

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_copy10_cons
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_copy10_nil

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[B.length+1] (some (cfg P 10 f h I O H C B))=
 some (cfg P 11 f none (B.reverse++I) O H C []):=by
 induction B generalizing h I with
 |nil=>simpa using copy10_nil P f h I O H C
 |cons a B ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,copy10_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
