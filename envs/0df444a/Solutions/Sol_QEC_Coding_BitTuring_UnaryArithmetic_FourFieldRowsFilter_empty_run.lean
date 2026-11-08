-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.empty_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:54:47.033947+00:00
-- url     : https://prove2.me/submissions/3da90291-14f8-48a3-903f-30424be7d7a0

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_peek_empty
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_drop13
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_q0_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_drain12_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_reverse14_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_qword_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (q:ℕ) (C:List Bool):
 (next P)^[2*(q+1)+C.tail.length+4]
  (some (cfg P 0 false none (qword q) [] [] C []))=
 some ((machine P).halt C.tail.reverse):=by
 rw [show 2*(q+1)+C.tail.length+4=
  (((C.tail.length+1)+1)+((qword q).reverse.length+1))+1+(q+1) by
  rw [List.length_reverse,qword_length];omega,Function.iterate_add_apply]
 have hq:=q0_run P hio false none q [] [] [] C []
 have hw:qword q=unary q++false::([]:List Bool):=by simp [qword]
 rw [hw,hq]
 simp only [List.append_nil]
 rw [Function.iterate_add_apply,Function.iterate_one]
 simp only [Option.bind_some,peek_empty P]
 rw [Function.iterate_add_apply,drain12_run P hio,Function.iterate_add_apply,Function.iterate_one]
 simp only [Option.bind_some,drop13 P hio]
 simpa using reverse14_run P hio false C.head? [] C.tail
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
