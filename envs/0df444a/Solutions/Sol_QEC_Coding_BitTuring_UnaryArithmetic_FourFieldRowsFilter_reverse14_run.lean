-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.reverse14_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:11:53.418464+00:00
-- url     : https://prove2.me/submissions/3c1ae6a5-12f6-4c56-8dbb-52aa6d8819df

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_reverse14_cons
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_reverse14_nil

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (O C:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[C.length+1] (some (cfg P 14 f h [] O [] C []))=
 some ((machine P).halt (C.reverse++O)):=by
 induction C generalizing h O with
 |nil=>simpa using reverse14_nil P hio f h O
 |cons a C ih=>
  rw [List.length_cons,Function.iterate_succ_apply]
  simp only [Option.bind_some,reverse14_cons P hio]
  rw [ih]
  simp only [List.reverse_cons,List.append_assoc,List.singleton_append]
  rfl
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
