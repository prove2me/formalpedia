-- Prove2me | solution 1 for QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter.after_run
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T09:54:45.457864+00:00
-- url     : https://prove2.me/submissions/79266fe9-1f12-44ab-b726-5a331c774fc3

import Definitions.Def_QEC_Coding_BitTuring_UnaryPrefixProjection
import Definitions.Def_QEC_Coding_BitTuring_FixedLiteral
import Definitions.Def_QEC_Coding_BitTuring_UnaryFieldProjection
import Definitions.Def_QEC_Coding_BitTuring_UnaryFourFieldRowsFilter
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_copy9_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_copy10_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_restore11_run
import Theorems.Thm_QEC_Coding_BitTuring_UnaryArithmetic_FourFieldRowsFilter_qword_length

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
open QEC.Coding.BitTuring QEC.Coding.BitTuring.UnaryArithmetic Turing StateTransition FieldProjection
variable (P:Machine)
namespace QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
theorem _root_.solution (hio:P.input≠P.output) (f:Bool) (h:Option Bool) (q:ℕ) (R C:List Bool):
 (next P)^[2*R.length+(q+1)+3]
  (some (cfg P 9 f h [] R (qword q).reverse C []))=
 some (cfg P 0 false none (qword q++R) [] [] C []):=by
 rw [show 2*R.length+(q+1)+3=((qword q).reverse.length+1)+(R.reverse.length+1)+(R.length+1) by
  rw [List.length_reverse,List.length_reverse,qword_length];omega,
  Function.iterate_add_apply,copy9_run P hio]
 simp only [List.append_nil]
 rw [Function.iterate_add_apply,copy10_run P hio]
 simp only [List.reverse_reverse,List.append_nil]
 rw [restore11_run P hio]
 simp only [List.reverse_reverse]
end QEC.Coding.BitTuring.UnaryArithmetic.FourFieldRowsFilter
