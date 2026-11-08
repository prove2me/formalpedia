-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsPrimeSquare_dvd_difference_or_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-07T11:59:48.773013+00:00
-- url     : https://prove2.me/submissions/c2e70a45-81ae-41ca-bb8f-ebba27db230f

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSQuaternionFactorization
import Mathlib.Algebra.Prime.Lemmas
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceFirstCoordinateCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (q a r : ℤ) (hq : Prime q)
    (hqr : ¬q ∣ 2*r) (h : q^2 ∣ (a-r)*(a+r)) : q^2 ∣ a-r ∨ q^2 ∣ a+r := by
  by_cases hm : q ∣ a-r
  · have hp : ¬q ∣ a+r := by
      intro hp
      apply hqr
      have hd : q ∣ (a+r)-(a-r) := dvd_sub hp hm
      have he : (a+r)-(a-r)=2*r := by ring
      rw [he] at hd
      exact hd
    exact Or.inl (hq.pow_dvd_of_dvd_mul_right 2 hp h)
  · exact Or.inr (hq.pow_dvd_of_dvd_mul_left 2 hm h)
end QEC.Coding.TannerLiftedProduct
