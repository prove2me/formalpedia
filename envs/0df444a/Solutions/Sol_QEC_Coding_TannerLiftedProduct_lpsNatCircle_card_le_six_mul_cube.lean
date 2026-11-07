-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_six_mul_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:02:39.086699+00:00
-- url     : https://prove2.me/submissions/cadfd6bc-c24f-4b19-897b-39e4238aceb3

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_card_le_boxes
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_card_le_coordinate_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_coordinates_bound
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s : Finset (ℕ × ℕ)) (n K : ℕ)
    (hK : 0 < K) (hn : n ≤ K^8) (hs : ∀ a ∈ s, a.1^2+a.2^2=n) :
    s.card ≤ 6*K^3 := by
  have hk3 : 0 < K^3 := pow_pos hK _
  by_cases hsmall : n ≤ 2*K^6
  · have hnR : n ≤ (2*K^3)^2 := by
      calc
        n ≤ 2*K^6 := hsmall
        _ ≤ 4*K^6 := by omega
        _ = (2*K^3)^2 := by ring
    have hc := lpsNatCircle_card_le_coordinate_bound s n (2*K^3) hs
      (fun a ha => (lpsNatCircle_coordinates_bound a n (2*K^3) (hs a ha) hnR).1)
    omega
  · have hnR : n ≤ (K^4)^2 := by simpa only [← pow_mul] using hn
    have hdiv : K^4/K=K^3 := by
      rw [show K^4=K^3*K by ring, Nat.mul_div_cancel _ hK]
    have hB : ∀ a ∈ s, a.1/K ≤ K^3 ∧ a.2/K ≤ K^3 := by
      intro a ha
      have hb := lpsNatCircle_coordinates_bound a n (K^4) (hs a ha) hnR
      constructor
      · simpa only [hdiv] using (Nat.div_le_div_right hb.1 : a.1/K ≤ K^4/K)
      · simpa only [hdiv] using (Nat.div_le_div_right hb.2 : a.2/K ≤ K^4/K)
    have hc := lpsNatCircle_card_le_boxes s n (K^3) K hK (by omega) hs hB
    omega
end QEC.Coding.TannerLiftedProduct
