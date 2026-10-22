-- Prove2me | solution 1 for RobustOdds.Tradeoff.final_bound
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:00:57.257234+00:00
-- url     : https://prove2.me/submissions/bf51965b-8042-4402-863e-d591d311376a

import Mathlib
import Definitions.Def_RobustOdds_Tradeoff_Setting

set_option autoImplicit false

theorem solution :
    ∀ p a b δ : ℝ, 1 / 2 ≤ p → p < 1 → 0 ≤ a →
      1 - δ ≤ 1 - 1 / 2 * (p * a + (1 - p) * b) →
      1 / 2 * ((1 - p) * a + p * b) ≤ p / (1 - p) * δ := by
  intro p a b δ hp hp1 ha h
  have hq : 0 < 1 - p := by linarith
  rw [div_mul_eq_mul_div p (1 - p) δ, le_div_iff₀ hq]
  have h1 : p * a + (1 - p) * b ≤ 2 * δ := by linarith
  have h2 : p * (p * a + (1 - p) * b) ≤ p * (2 * δ) :=
    mul_le_mul_of_nonneg_left h1 (by linarith)
  have h3 : 0 ≤ a * (p - (1 - p)) * (p + (1 - p)) :=
    mul_nonneg (mul_nonneg ha (by linarith)) (by linarith)
  nlinarith [h2, h3]
