-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerCircleThreeDistinct_distance_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:55:44.542865+00:00
-- url     : https://prove2.me/submissions/61f3322e-1f1b-4e34-ad76-2e5cd127bbaf

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleSquaredDistance_nonneg
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleChordCircumradius
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleThreeDistinct_det_ne_zero

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a b c : ℤ × ℤ) (n L : ℤ) (hn : 0 ≤ n)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (hab : a≠b) (hac : a≠c) (hbc : b≠c)
    (habL : lpsIntegerCircleSquaredDistance a b ≤ 2*L^2)
    (hacL : lpsIntegerCircleSquaredDistance a c ≤ 2*L^2)
    (hbcL : lpsIntegerCircleSquaredDistance b c ≤ 2*L^2) : n ≤ 2*L^6 := by
  have hdet : 1 ≤ (lpsIntegerCircleChordDet a b c)^2 := by
    have := sq_pos_of_ne_zero (lpsIntegerCircleThreeDistinct_det_ne_zero a b c n ha hb hc hab hac hbc)
    omega
  have hleft : 4*n ≤ 4*n*(lpsIntegerCircleChordDet a b c)^2 := by
    calc
      4*n = 4*n*1 := by ring
      _ ≤ 4*n*(lpsIntegerCircleChordDet a b c)^2 := mul_le_mul_of_nonneg_left hdet (by omega)
  have hab0 := lpsIntegerCircleSquaredDistance_nonneg a b
  have hac0 := lpsIntegerCircleSquaredDistance_nonneg a c
  have hbc0 := lpsIntegerCircleSquaredDistance_nonneg b c
  have hprod : lpsIntegerCircleSquaredDistance a b * lpsIntegerCircleSquaredDistance a c *
      lpsIntegerCircleSquaredDistance b c ≤ 8*L^6 := by
    calc
      _ ≤ (2*L^2)*(2*L^2)*(2*L^2) := by
        gcongr
      _ = 8*L^6 := by ring
  nlinarith [lpsIntegerCircleChordCircumradius a b c n ha hb hc]
end QEC.Coding.TannerLiftedProduct
