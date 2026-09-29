-- Prove2me | solution 1 for OnlineConvexOpt.GamesDuality.simple_lp_regret
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-09-25T07:54:06.275151+00:00
-- url     : https://prove2.me/submissions/524588e0-6e6c-455b-b965-cf7cbdaabb8b

import Mathlib
import Definitions.Def_OnlineConvexOpt_GamesDuality_Game

/-! Disproof of e3dc1f85 `OnlineConvexOpt.GamesDuality.simple_lp_regret`.

`lambdaR A = ⨅ x ∈ Δn, ⨆ y ∈ Δm, x⊤Ay`. Over `ℝ`, `⨅ x ∈ Δn, …` is `⨅ x, ⨅ (_ : x ∈ Δn), …`, and
for `x = 0 ∉ Δn` the inner infimum is over an empty index and equals `sInf ∅ = 0`. So
`lambdaR A ≤ 0` for every `A`. Take `n = m = T = 1` and `A = [1]`. Then `log 1 = 0`, so the rate
is `η = 0`, and the constant run `x t = y t = (1)` satisfies `IsSimpleLPRun`. At `y' = (1) ∈ Δ1`
the left side is `rowValue A (average x 1) y' = 1`, while the right side is
`lambdaR A + √(2 log 1)/√1 ≤ 0 + 0`. -/

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
theorem oco_dp_lambdaR_nonpos {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ) : lambdaR A ≤ 0 := by
  unfold lambdaR
  refine Real.iInf_nonpos' ⟨0, ?_⟩
  rw [ciInf_neg (oco_dp_zero_not_mem_stdSimplex n), Real.sInf_empty]

open OnlineConvexOpt.GamesDuality in
theorem solution : ¬ (∀ {n m T : ℕ} (hn : 0 < n) (hm : 0 < m) (hT : 0 < T)
    (A : Matrix (Fin n) (Fin m) ℝ) (hA : ∀ i j, |A i j| ≤ 1)
    (x : ℕ → Fin n → ℝ) (y : ℕ → Fin m → ℝ)
    (hrun : IsSimpleLPRun (Real.sqrt (2 * Real.log (n : ℝ) / (T : ℝ))) A x y),
    ∀ y' ∈ stdSimplex ℝ (Fin m),
      rowValue A (average x T) y' ≤
        lambdaR A + Real.sqrt (2 * Real.log (n : ℝ)) / Real.sqrt (T : ℝ)) := by
  intro H
  have key := H (n := 1) (m := 1) (T := 1) one_pos one_pos one_pos
    (Matrix.of (fun _ _ => (1 : ℝ))) (by intro i j; simp) (fun _ _ => 1) (fun _ _ => 1)
    (oco_dp_const_run _) (fun _ => 1) ⟨fun _ => zero_le_one, by simp⟩
  have hl := oco_dp_lambdaR_nonpos (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin 1) (Fin 1) ℝ)
  have hv : rowValue (Matrix.of (fun _ _ => (1 : ℝ)) : Matrix (Fin 1) (Fin 1) ℝ)
      (average (fun _ _ => 1) 1) (fun _ => 1) = 1 := by
    simp [rowValue, average, Matrix.mulVec, dotProduct]
  have hr : Real.sqrt (2 * Real.log ((1 : ℕ) : ℝ)) / Real.sqrt ((1 : ℕ) : ℝ) = 0 := by simp
  rw [hv, hr] at key
  linarith
