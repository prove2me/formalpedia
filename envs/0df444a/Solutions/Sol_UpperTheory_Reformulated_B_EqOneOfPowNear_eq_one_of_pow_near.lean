-- Prove2me | solution 1 for UpperTheory.Reformulated.B.EqOneOfPowNear.eq_one_of_pow_near
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:58.642751+00:00
-- url     : https://prove2.me/submissions/ad3b3190-8557-4d2f-bc25-02764413da84

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_EqOneOfPowNear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

namespace UpperTheory.Reformulated.B.EqOneOfPowNear
theorem _root_.solution :
    ∀ (z : ℂ),
    (∀ (n : ℕ), ‖z ^ n - (1 : ℂ)‖ < (1 / 2 : ℝ)) → z = (1 : ℂ) := by
  intro z h
  have step : ∀ n : ℕ, (3 / 2 : ℝ) * ‖z ^ n - 1‖ ≤ ‖z ^ (n * 2) - 1‖ := by
    intro n
    have e : z ^ (n * 2) - 1 = (z ^ n + 1) * (z ^ n - 1) := by ring
    have h1 : ‖(2 : ℂ)‖ ≤ ‖z ^ n + 1‖ + ‖z ^ n - 1‖ := by
      have e2 : (2 : ℂ) = (z ^ n + 1) - (z ^ n - 1) := by ring
      calc ‖(2 : ℂ)‖ = ‖(z ^ n + 1) - (z ^ n - 1)‖ := congrArg _ e2
        _ ≤ _ := norm_sub_le _ _
    have h2 : ‖(2 : ℂ)‖ = 2 := by simp
    have h3 := h n
    rw [e, norm_mul]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have grow : ∀ k : ℕ, (3 / 2 : ℝ) ^ k * ‖z - 1‖ ≤ ‖z ^ (2 ^ k) - 1‖ := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have s := step (2 ^ k)
      rw [pow_succ, pow_succ]
      linarith
  by_contra hz
  have hpos : 0 < ‖z - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hz)
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt ((1 / 2 : ℝ) / ‖z - 1‖) (by norm_num : (1 : ℝ) < 3 / 2)
  rw [div_lt_iff₀ hpos] at hk
  have g := grow k
  have h4 := h (2 ^ k)
  linarith
end UpperTheory.Reformulated.B.EqOneOfPowNear
