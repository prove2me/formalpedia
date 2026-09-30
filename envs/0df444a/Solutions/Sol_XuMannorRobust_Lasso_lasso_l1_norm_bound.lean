-- Prove2me | solution 1 for XuMannorRobust.Lasso.lasso_l1_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:15:59.860275+00:00
-- url     : https://prove2.me/submissions/7c2a9b5c-5873-4129-988d-536a8a6c0562

import Mathlib
import Definitions.Def_XuMannorRobust_Lasso_LassoFormulation
open XuMannorRobust.Lasso

theorem solution {m n : ℕ} (c : ℝ) (hc : 0 < c)
    (s : Fin n → ℝ × (Fin m → ℝ)) (w : Fin m → ℝ) (hw : IsLassoSolution c s w) :
    lassoObjective c s w ≤ lassoObjective c s 0 ∧
    lassoObjective c s 0 = (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 ∧
    l1norm w ≤ (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 := by
  have hzero : lassoObjective c s 0 = (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 := by
    simp [lassoObjective, l1norm]
  refine ⟨hw 0, hzero, ?_⟩
  have hnonneg : 0 ≤ (1 / (n : ℝ)) * ∑ i, ((s i).1 - dotProduct w (s i).2) ^ 2 := by
    positivity
  have hbound : c * l1norm w ≤ (1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2 := by
    have := hw 0
    rw [hzero] at this
    unfold lassoObjective at this
    linarith
  calc
    l1norm w ≤ ((1 / (n : ℝ)) * ∑ i, (s i).1 ^ 2) / c :=
      (le_div_iff₀ hc).mpr (by simpa [mul_comm] using hbound)
    _ = (1 / ((n : ℝ) * c)) * ∑ i, (s i).1 ^ 2 := by simp [div_eq_mul_inv]; ring
