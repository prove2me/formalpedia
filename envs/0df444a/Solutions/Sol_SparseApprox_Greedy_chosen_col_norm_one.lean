-- Prove2me | solution 1 for SparseApprox.Greedy.chosen_col_norm_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-28T22:57:55.705769+00:00
-- url     : https://prove2.me/submissions/a9c85add-0e2c-49b7-957a-1af728afd855

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one

open scoped InnerProductSpace
open SparseApprox.Greedy

private lemma selected_norm_one {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r < t) :
    ‖(greedyState A b k r).col (k r)‖ = 1 := by
  rcases state_col_norm_zero_or_one A b k r (k r) with hzero | hone
  · exfalso
    exact (hrun r hr).2.2.1 (by simp [hzero])
  · exact hone

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r ≤ t)
    {i : Fin n}
    (hi : i ∈ (greedyState A b k r).chosen) :
    ‖(greedyState A b k r).col i‖ = 1 := by
  induction r generalizing i with
  | zero =>
      simp [greedyState, initState] at hi
  | succ r ih =>
      have hrlt : r < t := Nat.lt_of_succ_le hr
      have hrle : r ≤ t := Nat.le_of_lt hrlt
      have hiNew :
          i = k r ∨ i ∈ (greedyState A b k r).chosen := by
        simpa [greedyState, greedyStep] using hi
      have hcoli :
          (greedyState A b k (r + 1)).col i =
            (greedyState A b k r).col i := by
        simp [greedyState, greedyStep, hiNew]
      rw [hcoli]
      rcases hiNew with rfl | hiOld
      · exact selected_norm_one A b ε k t r hrun hrlt
      · exact ih hrle hiOld
