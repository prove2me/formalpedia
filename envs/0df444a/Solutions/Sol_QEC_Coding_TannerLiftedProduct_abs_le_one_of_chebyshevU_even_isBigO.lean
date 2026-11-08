-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.abs_le_one_of_chebyshevU_even_isBigO
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T12:51:18.789073+00:00
-- url     : https://prove2.me/submissions/4c983215-26bd-475f-b7e8-56547068da43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSExactTraceFormula
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSSpectralTrace
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSRamanujanTraceBridge
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_abs_le_of_chebyshevU_even_isBigO

set_option autoImplicit false
open Polynomial
open scoped MatrixGroups
open Filter Asymptotics
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x : ℝ)
    (h : ∀ s : ℝ, 1 < s →
      (fun n : ℕ =>
        (Polynomial.Chebyshev.U ℝ (2 * (n : ℤ))).eval x) =O[atTop]
          fun n : ℕ => s ^ (2 * n)) :
    |x| ≤ 1 :=
  abs_le_of_chebyshevU_even_isBigO x 1 (by norm_num) h
end QEC.Coding.TannerLiftedProduct
