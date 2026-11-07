-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerCircleSquaredDistance_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:35.874068+00:00
-- url     : https://prove2.me/submissions/11ff1fcc-a5bb-456b-8f12-60805386692a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a b : ℤ × ℤ) :
    lpsIntegerCircleSquaredDistance a b = 0 ↔ a = b := by
  constructor
  · intro h
    have hx : (b.1-a.1)^2=0 := by
      unfold lpsIntegerCircleSquaredDistance at h
      nlinarith [sq_nonneg (b.2-a.2)]
    have hy : (b.2-a.2)^2=0 := by
      unfold lpsIntegerCircleSquaredDistance at h
      nlinarith [sq_nonneg (b.1-a.1)]
    exact Prod.ext (sub_eq_zero.mp (sq_eq_zero_iff.mp hx)).symm
      (sub_eq_zero.mp (sq_eq_zero_iff.mp hy)).symm
  · rintro rfl
    simp [lpsIntegerCircleSquaredDistance]
end QEC.Coding.TannerLiftedProduct
