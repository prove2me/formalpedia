-- Prove2me | solution 1 for StochCoordProx.display_56_mgf_inequality
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-31T14:08:37.328786+00:00
-- url     : https://prove2.me/submissions/709b71c6-aaa1-43c4-b774-42d1c15bc554

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

private lemma exp_neg_le_quad (y : ℝ) (hy : 0 ≤ y) :
    Real.exp (-y) ≤ 1 - y + y ^ 2 / 2 := by
  let h : ℝ → ℝ := fun t => 1 - t + t ^ 2 / 2 - Real.exp (-t)
  have hderiv : ∀ t : ℝ, HasDerivAt h (0 - 1 + (2 * t ^ (2 - 1)) / 2 - (Real.exp (-t) * -1)) t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => (1 : ℝ) - s) (0 - 1) t :=
      (hasDerivAt_const t (1 : ℝ)).sub (hasDerivAt_id t)
    have h2 : HasDerivAt (fun s : ℝ => s ^ 2 / 2) ((2 * t ^ (2 - 1)) / 2) t :=
      (hasDerivAt_pow 2 t).div_const 2
    have h3 : HasDerivAt (fun s : ℝ => Real.exp (-s)) (Real.exp (-t) * -1) t :=
      HasDerivAt.exp (HasDerivAt.neg (hasDerivAt_id t))
    exact (h1.add h2).sub h3
  have hmono : Monotone h := by
    refine monotone_of_hasDerivAt_nonneg hderiv ?_
    intro t
    dsimp
    have ht : 2 * t ^ (2 - 1) / 2 = t := by ring
    have hexp := Real.add_one_le_exp (-t)
    linarith
  have h0 : h 0 ≤ h y := hmono hy
  have h0_eq : h 0 = 0 := by simp [h]
  rw [h0_eq] at h0
  dsimp [h] at h0
  linarith

theorem solution (p y : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hy : 0 ≤ y) :
    p * y + Real.log (1 - p + p * Real.exp (-y)) ≤ y ^ 2 * p / 2 := by
  have hpos : 0 < 1 - p + p * Real.exp (-y) := by
    rcases eq_or_lt_of_le hp0 with rfl | hp_pos
    · simp
    · have hexp : 0 < p * Real.exp (-y) := mul_pos hp_pos (Real.exp_pos _)
      linarith
  have hlog : Real.log (1 - p + p * Real.exp (-y)) ≤ p * (Real.exp (-y) - 1) := by
    have := Real.log_le_sub_one_of_pos hpos
    linarith
  have hexp := exp_neg_le_quad y hy
  have hp_quad : p * (y + Real.exp (-y) - 1) ≤ p * (y ^ 2 / 2) :=
    mul_le_mul_of_nonneg_left (by linarith) hp0
  linarith
