-- Prove2me | solution 1 for SlowConvergence.ARC.phi_mem
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T11:23:40.671+00:00
-- url     : https://prove2.me/submissions/afb42a87-99ce-4dc1-9cf1-946f839a0b14

import Mathlib
import Definitions.Def_SlowConvergence_ARC_Data
import Definitions.Def_SlowConvergence_ARC_Pieces

set_option autoImplicit false
open SlowConvergence.ARC

theorem solution (τ : ℝ) (hτ0 : 0 < τ) (hτ1 : τ < 1) (k : ℕ) :
    0 < phi τ k ∧ phi τ k < 1 := by
  have hη : 0 < eta τ := by
    unfold eta
    have h : 2 / 3 < 2 / (3 - 2 * τ) := by
      rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    linarith
  have hμ : 0 < mu τ := by unfold mu; linarith
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hk2 : (0 : ℝ) < (k : ℝ) + 2 := by positivity
  have hphi : phi τ k = 1 - (((k : ℝ) + 1) * (1 / ((k : ℝ) + 2))) ^ mu τ := by
    unfold phi
    rw [mul_sub, ← Real.mul_rpow hk1.le (by positivity), ← Real.mul_rpow hk1.le (by positivity)]
    have : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 1)) = 1 := by field_simp
    rw [this, Real.one_rpow]
  have hr0 : 0 < ((k : ℝ) + 1) * (1 / ((k : ℝ) + 2)) := by positivity
  have hr1 : ((k : ℝ) + 1) * (1 / ((k : ℝ) + 2)) < 1 := by
    rw [mul_one_div, div_lt_one hk2]; linarith
  rw [hphi]
  have h1 := Real.rpow_lt_one hr0.le hr1 hμ
  have h2 := Real.rpow_pos_of_pos hr0 (mu τ)
  constructor <;> linarith
