-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircle_firstCoordinate_injOn
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:59.451363+00:00
-- url     : https://prove2.me/submissions/1a883b96-e360-4b92-ab6e-b9ed47c2b72d

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
theorem _root_.solution (s : Finset (ℕ × ℕ)) (n : ℕ)
    (hs : ∀ a ∈ s, a.1^2+a.2^2=n) : (s : Set (ℕ × ℕ)).InjOn Prod.fst := by
  intro a ha b hb h
  have haN := hs a ha
  have hbN := hs b hb
  have hsq : a.2^2=b.2^2 := by change a.1=b.1 at h; rw [h] at haN; omega
  exact Prod.ext h (by simpa only [Nat.sqrt_eq'] using congrArg Nat.sqrt hsq)
end QEC.Coding.TannerLiftedProduct
