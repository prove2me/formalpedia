-- Prove2me | solution 1 for RelSmoothFOM.DualAvg.weight_identity
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T06:24:28.583713+00:00
-- url     : https://prove2.me/submissions/9db8a54c-ce99-4e80-ae25-d3dda15c268d

import Mathlib
import Definitions.Def_RelSmoothFOM_DualAvg_Setting

set_option autoImplicit false
open RelSmoothFOM.DualAvg

theorem solution (L μ : ℝ) (hμ : 0 ≤ μ) (hμL : μ < L) (k : ℕ) :
    μ + 1 / daWeight L μ k * (1 + μ * daSum L μ k) =
        (1 + μ * daSum L μ (k + 1)) / daWeight L μ k ∧
      (1 + μ * daSum L μ (k + 1)) / daWeight L μ k =
        1 / daWeight L μ k * (L / (L - μ)) ^ (k + 1) ∧
      1 / daWeight L μ k * (L / (L - μ)) ^ (k + 1) = L := by
  have hd : 0 < L - μ := by linarith
  have hL : 0 < L := by linarith
  have hr : 0 < L / (L - μ) := div_pos hL hd
  have ha : 0 < daWeight L μ k := by
    unfold daWeight; positivity
  have hstep : ∀ j : ℕ, daSum L μ (j + 1) = daSum L μ j + daWeight L μ j := by
    intro j; simp [daSum, Finset.sum_range_succ]
  have key : ∀ j : ℕ, 1 + μ * daSum L μ j = (L / (L - μ)) ^ j := by
    intro j
    induction j with
    | zero => simp [daSum]
    | succ j ih =>
      rw [hstep, mul_add, ← add_assoc, ih, daWeight, pow_succ]
      field_simp
      ring
  refine ⟨?_, ?_, ?_⟩
  · rw [hstep]
    field_simp
    ring
  · rw [key (k + 1)]
    ring
  · unfold daWeight
    rw [div_pow, pow_succ, div_pow]
    have hp : 0 < (L - μ) ^ k := by positivity
    field_simp
