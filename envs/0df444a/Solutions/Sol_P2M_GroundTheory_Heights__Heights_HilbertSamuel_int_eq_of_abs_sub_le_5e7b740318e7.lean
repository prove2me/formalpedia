-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_int_eq_of_abs_sub_le_5e7b740318e7
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:26:41.59558+00:00
-- url     : https://prove2.me/submissions/ef33c9a4-cb77-4dee-a2f7-a197dca8b587

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsHilbert
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PHilbertPrime

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
open MvPolynomial GroundTheory.Heights₂.Heights.NumbersDVR
noncomputable section
universe u
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
theorem _root_.solution {z₁ z₂ : ℤ} {c s : ℝ} (hs : 0 ≤ s) (hc : |c| < s + 1)
    (h : |(z₁ : ℝ) - (z₂ : ℝ)| ≤ c * (s + 1) ^ (((0 : ℕ) : ℝ) - 1)) : z₁ = z₂ := by
  rw [Nat.cast_zero, zero_sub, Real.rpow_neg_one] at h
  rw [← sub_eq_zero]
  set z := z₁ - z₂
  have hz : (z : ℝ) = (z₁ : ℝ) - (z₂ : ℝ) := by push_cast [z]; rfl
  rw [← hz] at h
  have hpos : 0 < s + 1 := by linarith
  have h1 : c * (s + 1)⁻¹ < 1 := by
    rw [← div_eq_mul_inv, div_lt_one hpos]
    exact lt_of_le_of_lt (le_abs_self c) hc
  have h2 : |(z : ℝ)| < 1 := lt_of_le_of_lt h h1
  rw [← Int.cast_abs] at h2
  have h3 : |z| < 1 := by exact_mod_cast h2
  exact Int.abs_lt_one_iff.mp h3
end GroundTheory.Heights₂.Heights.HilbertSamuel
