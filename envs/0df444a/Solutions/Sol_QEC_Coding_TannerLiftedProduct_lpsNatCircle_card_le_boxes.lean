-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_boxes
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T22:01:38.48656+00:00
-- url     : https://prove2.me/submissions/0ef09942-810d-43d7-9332-74915311aaa9

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircleBoxRank_fiber_card_le_two
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s : Finset (ℕ × ℕ)) (n M L : ℕ)
    (hL : 0 < L) (hsmall : 2*L^6 < n)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n)
    (hB : ∀ a ∈ s, a.1/L ≤ M ∧ a.2/L ≤ M) : s.card ≤ 2*(2*M+1) := by
  classical
  have hmap : ∀ a ∈ s, lpsNatCircleBoxRank M L a ∈ Finset.range (2*M+1) := by
    intro a ha
    have hr : lpsNatCircleBoxRank M L a ≤ M+M :=
      Nat.add_le_add (hB a ha).1 (Nat.sub_le M _)
    exact Finset.mem_range.mpr (by omega)
  have hh := Finset.card_le_mul_card_image_of_maps_to hmap 2
    (fun j _ => lpsNatCircleBoxRank_fiber_card_le_two s n M L j hL hsmall hs hB)
  simpa using hh
end QEC.Coding.TannerLiftedProduct
