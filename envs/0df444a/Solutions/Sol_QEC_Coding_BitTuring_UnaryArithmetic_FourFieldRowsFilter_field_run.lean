-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.field_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:12:30.121811+00:00
-- url     : https://prove2.me/submissions/38d6fb53-d3ce-4df8-811d-c30f06e791fc

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_field_bit
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_field_sep

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (k:Fin 4) (f:Bool) (h:Option Bool) (a:ℕ)
 (I O H C B:List Bool):
 (fun c:Option (TM2.Cfg (fun _:Stack P=>Bool) (Label P) (Var P))=>c.bind (TM2.step (program P)))^[a+1]
  (some (cfg P ⟨5+k.val,by omega⟩ f h I (unary a++false::O) H C B))=
 some (cfg P ⟨6+k.val,by omega⟩ f (some false) I O H (pushed f (unary a++[false]) C) B):=by
 induction a generalizing h C with
 |zero=>simpa [unary,pushed] using field_sep P hio k f h I O H C B
 |succ a ih=>
  simp only [unary_succ,List.cons_append]
  rw [Function.iterate_succ_apply]
  simp only [Option.bind_some,field_bit P hio]
  rw [ih]
  cases f <;>simp [pushed,List.reverse_cons,List.append_assoc]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
