-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerCircleThinBox_no_three_distinct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:56:57.965652+00:00
-- url     : https://prove2.me/submissions/c81e5ec3-c6a0-46f2-89d2-3391f76e8c43

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleSquaredDistance_le_of_abs_bounds
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsIntegerCircleThreeDistinct_distance_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (a b c : ℤ × ℤ) (n L : ℤ) (hn : 0 ≤ n) (hL : 0 ≤ L) (hsmall : 2*L^6<n)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n) (hc : c.1^2+c.2^2=n)
    (habx : |b.1-a.1| ≤ L) (haby : |b.2-a.2| ≤ L)
    (hacx : |c.1-a.1| ≤ L) (hacy : |c.2-a.2| ≤ L)
    (hbcx : |c.1-b.1| ≤ L) (hbcy : |c.2-b.2| ≤ L) :
    a=b ∨ a=c ∨ b=c := by
  by_contra h
  push Not at h
  have hbound := lpsIntegerCircleThreeDistinct_distance_bound a b c n L hn ha hb hc h.1 h.2.1 h.2.2
    (lpsIntegerCircleSquaredDistance_le_of_abs_bounds a b L hL habx haby)
    (lpsIntegerCircleSquaredDistance_le_of_abs_bounds a c L hL hacx hacy)
    (lpsIntegerCircleSquaredDistance_le_of_abs_bounds b c L hL hbcx hbcy)
  omega
end QEC.Coding.TannerLiftedProduct
