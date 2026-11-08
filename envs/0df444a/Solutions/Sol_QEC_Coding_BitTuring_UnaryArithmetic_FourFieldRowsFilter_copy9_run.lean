-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.copy9_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:11:26.272719+00:00
-- url     : https://prove2.me/submissions/0b1034f9-e06f-41de-9020-a9c45a5e41da

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_copy9_cons
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_copy9_nil

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[O.length+1] (some (cfg P 9 f h I O H C B))=
 some (cfg P 10 f none I [] H C (O.reverse++B)):=by
 induction O generalizing h B with
 |nil=>simpa using copy9_nil P hio f h I H C B
 |cons a O ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,copy9_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
