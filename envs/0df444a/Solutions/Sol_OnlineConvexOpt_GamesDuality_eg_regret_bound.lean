-- Prove2me | solution 1 for OnlineConvexOpt.GamesDuality.eg_regret_bound
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T07:52:51.726754+00:00
-- url     : https://prove2.me/submissions/68f122f3-8c5b-4dfc-8595-78fdd0a3b6ea

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game

/-! Disproof of da6d12b2 `OnlineConvexOpt.GamesDuality.eg_regret_bound`.

The comparator `⨅ x' ∈ stdSimplex ℝ (Fin n), S x'` is, over `ℝ`, `⨅ x', ⨅ (_ : x' ∈ Δ), S x'`.
For `x' = 0 ∉ Δ` the inner infimum is over an empty index and equals `sInf ∅ = 0`, so the
whole comparator is `≤ 0`. Take `n = m = T = 1` and `A = [1]`. Then `log 1 = 0`, so the rate
is `η = 0`, and the constant run `x t = y t = (1)` satisfies `IsSimpleLPRun`. The left side is
`1`, while the right side is `(⨅ …) + √(2·1·log 1) ≤ 0 + 0`. -/

set_option autoImplicit false

theorem oco_dp_zero_not_mem_stdSimplex (k : ℕ) : (0 : Fin k → ℝ) ∉ stdSimplex ℝ (Fin k) := by
  intro h
  have h1 := h.2
  simp at h1

open OnlineConvexOpt.GamesDuality in
theorem oco_dp_const_run (η : ℝ) :
    IsSimpleLPRun η (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin 1) (Fin 1) ℝ)
      (fun _ _ => 1) (fun _ _ => 1) where
  init := by intro i; simp
  best_response := by
    intro t
    refine ⟨⟨fun _ => zero_le_one, by simp⟩, ?_⟩
    intro y' hy'
    have hs := hy'.2
    simp only [Fin.sum_univ_one] at hs
    simp [rowValue, Matrix.mulVec, dotProduct, hs]
  update := by
    intro t i
    simp only [Fin.sum_univ_one, one_mul]
    rw [Subsingleton.elim i 0, div_self (Real.exp_ne_zero _)]

open OnlineConvexOpt.GamesDuality in
theorem solution : ¬ (∀ {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y),
    ∑ t ∈ Finset.range T, rowValue A (x t) (y t) ≤
      (⨅ x' ∈ stdSimplex ℝ (Fin n), ∑ t ∈ Finset.range T, rowValue A x' (y t)) +
        Real.sqrt (2 * (T : ℝ) * Real.log (n : ℝ))) := by
  intro H
  have key := H (n := 1) (m := 1) (T := 1) one_pos one_pos one_pos
    (Matrix.of (fun _ _ => (1 : ℝ))) (by intro i j; simp) (fun _ _ => 1) (fun _ _ => 1)
    (oco_dp_const_run _)
  have hinf : (⨅ x' ∈ stdSimplex ℝ (Fin 1), ∑ t ∈ Finset.range 1,
      rowValue (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin 1) (Fin 1) ℝ) x'
        ((fun _ _ => 1 : ℕ → Fin 1 → ℝ) t)) ≤ 0 := by
    refine Real.iInf_nonpos' ⟨0, ?_⟩
    rw [ciInf_neg (oco_dp_zero_not_mem_stdSimplex 1), Real.sInf_empty]
  have hl : ∑ t ∈ Finset.range 1, rowValue (Matrix.of (fun _ _ => (1 : ℝ)) :
      Matrix (Fin 1) (Fin 1) ℝ) ((fun _ _ => 1 : ℕ → Fin 1 → ℝ) t)
        ((fun _ _ => 1 : ℕ → Fin 1 → ℝ) t) = 1 := by
    simp [rowValue, Matrix.mulVec, dotProduct]
  have hr : Real.sqrt (2 * ((1 : ℕ) : ℝ) * Real.log ((1 : ℕ) : ℝ)) = 0 := by simp
  rw [hl, hr] at key
  linarith
