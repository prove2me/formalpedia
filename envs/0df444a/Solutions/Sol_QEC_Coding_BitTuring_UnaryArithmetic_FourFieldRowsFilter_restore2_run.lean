-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.restore2_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:11:47.44762+00:00
-- url     : https://prove2.me/submissions/52ad5e6c-19bf-4691-82d0-4c8d1f560f3b

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_restore2_cons
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_restore2_nil

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I H C:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[H.length+1] (some (cfg P 2 f h I [] H C []))=
 some (embedBody P C (P.init (H.reverse++I))):=by
 induction H generalizing h I with
 |nil=>simpa using restore2_nil P hio f h I C
 |cons a H ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,restore2_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
