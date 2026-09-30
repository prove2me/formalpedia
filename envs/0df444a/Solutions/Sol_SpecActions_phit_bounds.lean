-- Prove2me | solution 1 for SpecActions.phit_bounds
-- status  : ACCEPTED   (prove)
-- author  : @naimengye
-- created : 2026-09-11T15:54:28.972868+00:00
-- url     : https://prove2.me/submissions/08b15e5b-6c3a-420e-babb-cea39eb26ff0

import Definitions.Def_SpecActions_model

open SpecActions

theorem solution (k : ℕ) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    0 ≤ phit k p ∧ phit k p ≤ 1 ∧ phit k p ≤ phit (k + 1) p := by
  have h0 : (0:ℝ) ≤ 1 - p := by linarith
  have h1 : (1:ℝ) - p ≤ 1 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · have : (1 - p) ^ k ≤ 1 := pow_le_one₀ h0 h1
    simp only [phit]; linarith
  · have : (0:ℝ) ≤ (1 - p) ^ k := pow_nonneg h0 k
    simp only [phit]; linarith
  · have : (1 - p) ^ (k + 1) ≤ (1 - p) ^ k :=
      pow_le_pow_of_le_one h0 h1 (Nat.le_succ k)
    simp only [phit]; linarith
