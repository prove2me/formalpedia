-- Prove2me | solution 1 for UpperTheory.Reformulated.B.P6.r23b.pow_mul_exp_le_half_exp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T15:46:54.434912+00:00
-- url     : https://prove2.me/submissions/aac5f267-4a6f-4d74-9747-275811f7cdeb

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SchwartzBilinear_PowMulExpLeHalfExp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperTheory UpperTheory.Reformulated UpperTheory.Reformulated.B UpperTheory.Reformulated.B.P6 UpperTheory.Reformulated.B.P6.r23b
namespace UpperTheory.Reformulated.B.P6.r23b
theorem _root_.solution (N : ℕ) (a : ℝ) (ha : 0 < a) :
    ∃ (C : ℝ), 0 ≤ C ∧ ∀ (x : ℝ), 0 ≤ x →
      (1 + x) ^ N * Real.exp (-(a * x)) ≤ C * Real.exp (-(a / 2 * x)) := by
  refine ⟨(2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2), by positivity, ?_⟩
  intro x hx
  have hy : 0 ≤ a / 2 * (1 + x) := by positivity
  have h1 : (a / 2 * (1 + x)) ^ N / (N.factorial : ℝ) ≤ Real.exp (a / 2 * (1 + x)) := Real.pow_div_factorial_le_exp (x := a / 2 * (1 + x)) (n := N) hy
  have hf : (0 : ℝ) < (N.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos N
  have h1' : (a / 2 * (1 + x)) ^ N ≤ Real.exp (a / 2 * (1 + x)) * (N.factorial : ℝ) :=
    (div_le_iff₀ hf).mp h1
  have h2 : (1 + x) ^ N = (2 / a) ^ N * (a / 2 * (1 + x)) ^ N := by
    rw [← mul_pow]
    congr 1
    field_simp
  have hp : (0 : ℝ) ≤ (2 / a) ^ N := by positivity
  have h3 : (1 + x) ^ N ≤ (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x)) := by
    rw [h2]
    have := mul_le_mul_of_nonneg_left h1' hp
    linarith [this]
  have h4 : Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x)) =
      Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc (1 + x) ^ N * Real.exp (-(a * x))
      ≤ ((2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2 * (1 + x))) * Real.exp (-(a * x)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_pos _).le
    _ = (2 / a) ^ N * (N.factorial : ℝ) * (Real.exp (a / 2 * (1 + x)) * Real.exp (-(a * x))) := by ring
    _ = (2 / a) ^ N * (N.factorial : ℝ) * Real.exp (a / 2) * Real.exp (-(a / 2 * x)) := by
        rw [h4]; ring
end UpperTheory.Reformulated.B.P6.r23b
