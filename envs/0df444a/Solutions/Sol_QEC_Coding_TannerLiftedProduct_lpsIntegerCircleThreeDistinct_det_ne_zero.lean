-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerCircleThreeDistinct_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:37.878519+00:00
-- url     : https://prove2.me/submissions/2d4f12a7-c436-4f98-b581-7c1c4c0df44a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleSquaredDistance_eq_zero_iff
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleChordCircumradius

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a b c : ℤ × ℤ) (n : ℤ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c) :
    lpsIntegerCircleChordDet a b c ≠ 0 := by
  intro h
  have hprod := lpsIntegerCircleChordCircumradius a b c n ha hb hc
  have hp0 : lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
      lpsIntegerCircleSquaredDistance b c = 0 := by
    calc
      _ = 4*n*(lpsIntegerCircleChordDet a b c)^2 := hprod.symm
      _ = 0 := by rw [h]; ring
  exact (mul_ne_zero
    (mul_ne_zero ((lpsIntegerCircleSquaredDistance_eq_zero_iff a b).not.mpr hab)
      ((lpsIntegerCircleSquaredDistance_eq_zero_iff a c).not.mpr hac))
    ((lpsIntegerCircleSquaredDistance_eq_zero_iff b c).not.mpr hbc)) hp0
end QEC.Coding.TannerLiftedProduct
