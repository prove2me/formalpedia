-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircle_card_le_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:54.551876+00:00
-- url     : https://prove2.me/submissions/131e23c0-a8bd-43bc-8add-58539546ad6d

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_firstCoordinate_injOn
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (s : Finset (ℕ × ℕ)) (n R : ℕ)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n) (hR : ∀ a ∈ s, a.1 ≤ R) : s.card ≤ R+1 := by
  classical
  have hm : Set.MapsTo Prod.fst (s : Set (ℕ × ℕ)) (Finset.range (R+1) : Set ℕ) := by
    intro a ha
    exact Finset.mem_range.mpr (by have := hR a ha; omega)
  simpa using Finset.card_le_card_of_injOn Prod.fst hm (lpsNatCircle_firstCoordinate_injOn s n hs)
end QEC.Coding.TannerLiftedProduct
