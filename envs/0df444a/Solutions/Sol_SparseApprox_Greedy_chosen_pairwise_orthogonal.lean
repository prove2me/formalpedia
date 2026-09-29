-- Prove2me | solution 1 for SparseApprox.Greedy.chosen_pairwise_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T01:31:14.616378+00:00
-- url     : https://prove2.me/submissions/2691cd89-4bbc-4752-8a3b-9553fd67b630

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one
import Theorems.Thm_SparseApprox_Greedy_chosen_col_norm_one
import Theorems.Thm_SparseApprox_Greedy_chosen_orthogonal_unchosen

open scoped InnerProductSpace
open SparseApprox.Greedy

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ)
    (k : ℕ → Fin n) (t r : ℕ)
    (hrun : IsGreedyRun A b ε k t) (hr : r ≤ t)
    {i j : Fin n}
    (hi : i ∈ (greedyState A b k r).chosen)
    (hj : j ∈ (greedyState A b k r).chosen)
    (hij : i ≠ j) :
    ⟪(greedyState A b k r).col i,
      (greedyState A b k r).col j⟫_ℝ = 0 := by
  induction r generalizing i j with
  | zero =>
      simp [greedyState, initState] at hi
  | succ r ih =>
      have hrlt : r < t := Nat.lt_of_succ_le hr
      have hrle : r ≤ t := Nat.le_of_lt hrlt
      have hknot :
          k r ∉ (greedyState A b k r).chosen :=
        (hrun r hrlt).2.1
      have hiNew :
          i = k r ∨ i ∈ (greedyState A b k r).chosen := by
        simpa [greedyState, greedyStep] using hi
      have hjNew :
          j = k r ∨ j ∈ (greedyState A b k r).chosen := by
        simpa [greedyState, greedyStep] using hj
      have hcoli :
          (greedyState A b k (r + 1)).col i =
            (greedyState A b k r).col i := by
        simp [greedyState, greedyStep, hiNew]
      have hcolj :
          (greedyState A b k (r + 1)).col j =
            (greedyState A b k r).col j := by
        simp [greedyState, greedyStep, hjNew]
      rw [hcoli, hcolj]
      rcases hiNew with rfl | hiOld
      · rcases hjNew with hsame | hjOld
        · exact (hij hsame.symm).elim
        · rw [real_inner_comm]
          exact chosen_orthogonal_unchosen
            A b ε k t r hrun hrle hjOld hknot
      · rcases hjNew with rfl | hjOld
        · exact chosen_orthogonal_unchosen
            A b ε k t r hrun hrle hiOld hknot
        · exact ih hrle hiOld hjOld hij
