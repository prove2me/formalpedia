-- Prove2me | solution 1 for SparseApprox.Greedy.chosen_residual_orthogonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T01:22:46.649095+00:00
-- url     : https://prove2.me/submissions/6c1fb9c3-2695-425e-9a88-7de60416cadd

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one
import Theorems.Thm_SparseApprox_Greedy_chosen_col_norm_one
import Theorems.Thm_SparseApprox_Greedy_chosen_orthogonal_unchosen

open scoped InnerProductSpace
open SparseApprox.Greedy

private lemma inner_reject_self {m : ℕ}
    (a x : EuclideanSpace ℝ (Fin m)) (ha : ‖a‖ = 1) :
    ⟪a, x - ⟪a, x⟫_ℝ • a⟫_ℝ = 0 := by
  rw [inner_sub_right, real_inner_smul_right,
    real_inner_self_eq_norm_sq, ha]
  ring

private lemma inner_reject_of_orthogonal {m : ℕ}
    (x a y : EuclideanSpace ℝ (Fin m))
    (hxy : ⟪x, y⟫_ℝ = 0) (hxa : ⟪x, a⟫_ℝ = 0) :
    ⟪x, y - ⟪a, y⟫_ℝ • a⟫_ℝ = 0 := by
  rw [inner_sub_right, real_inner_smul_right, hxy, hxa]
  ring

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
    {i : Fin n} (hi : i ∈ (greedyState A b k r).chosen) :
    ⟪(greedyState A b k r).col i,
      (greedyState A b k r).res⟫_ℝ = 0 := by
  induction r generalizing i with
  | zero =>
      simp [greedyState, initState] at hi
  | succ r ih =>
      have hrlt : r < t := Nat.lt_of_succ_le hr
      have hrle : r ≤ t := Nat.le_of_lt hrlt
      have hknot :
          k r ∉ (greedyState A b k r).chosen :=
        (hrun r hrlt).2.1
      have hknorm :
          ‖(greedyState A b k r).col (k r)‖ = 1 :=
        selected_norm_one A b ε k t r hrun hrlt
      have hiNew :
          i = k r ∨ i ∈ (greedyState A b k r).chosen := by
        simpa [greedyState, greedyStep] using hi
      have hcoli :
          (greedyState A b k (r + 1)).col i =
            (greedyState A b k r).col i := by
        simp [greedyState, greedyStep, hiNew]
      have hres :
          (greedyState A b k (r + 1)).res =
            (greedyState A b k r).res -
              ⟪(greedyState A b k r).col (k r),
                (greedyState A b k r).res⟫_ℝ •
                (greedyState A b k r).col (k r) := by
        simp [greedyState, greedyStep]
      rw [hcoli, hres]
      rcases hiNew with rfl | hiOld
      · exact inner_reject_self _ _ hknorm
      · exact inner_reject_of_orthogonal _ _ _
          (ih hrle hiOld)
          (chosen_orthogonal_unchosen
            A b ε k t r hrun hrle hiOld hknot)
