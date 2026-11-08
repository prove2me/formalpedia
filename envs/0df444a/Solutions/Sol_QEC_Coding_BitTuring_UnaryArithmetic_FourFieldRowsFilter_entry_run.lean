-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.entry_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:54:06.619421+00:00
-- url     : https://prove2.me/submissions/00f36836-5b0d-40a3-8880-f4588448d134

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_peek_more
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_q0_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_restore2_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_qword_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (q:ℕ) (s C:List Bool) (hs:s≠[]):
 (next P)^[2*(q+1)+2] (some (cfg P 0 false none (qword q++s) [] [] C []))=
 some (embedBody P C (P.init (qword q++s))):=by
 cases s with
 |nil=>exact (hs rfl).elim
 |cons a s=>
  rw [show 2*(q+1)+2=((qword q).reverse.length+1)+1+(q+1) by rw [List.length_reverse,qword_length];omega,
   Function.iterate_add_apply]
  have hq:=q0_run P hio false none q (a::s) [] [] C []
  have hw:qword q++a::s=unary q++false::(a::s):=by simp [qword,List.append_assoc]
  rw [hw,hq]
  simp only [List.append_nil]
  rw [Function.iterate_add_apply,Function.iterate_one]
  simp only [Option.bind_some,peek_more P]
  simpa only [qword,List.reverse_reverse,List.append_assoc,List.cons_append,List.singleton_append,List.nil_append] using
   restore2_run P hio false (some a) (a::s) (qword q).reverse C
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
