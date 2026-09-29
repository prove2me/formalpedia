-- Prove2me | solution 1 for SparseApprox.Greedy.chosen_orthogonal_unchosen
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-29T01:05:27.012896+00:00
-- url     : https://prove2.me/submissions/18630b78-1392-459d-a9b8-d41e27218306

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm
import Theorems.Thm_SparseApprox_Greedy_state_col_norm_zero_or_one
import Theorems.Thm_SparseApprox_Greedy_chosen_col_norm_one

open scoped InnerProductSpace
open SparseApprox.Greedy

private lemma inner_normalize_reject_self {m : ℕ}
    (a x : EuclideanSpace ℝ (Fin m)) (ha : ‖a‖ = 1) :
    ⟪a, normalizeVec (x - ⟪a, x⟫_ℝ • a)⟫_ℝ = 0 := by
  rw [normalizeVec, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, ha]
  ring

private lemma inner_normalize_reject_of_orthogonal {m : ℕ}
    (x a y : EuclideanSpace ℝ (Fin m))
    (hxy : ⟪x, y⟫_ℝ = 0) (hxa : ⟪x, a⟫_ℝ = 0) :
    ⟪x, normalizeVec (y - ⟪a, y⟫_ℝ • a)⟫_ℝ = 0 := by
  rw [normalizeVec, real_inner_smul_right, inner_sub_right,
    real_inner_smul_right, hxy, hxa]
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
    {i j : Fin n}
    (hi : i ∈ (greedyState A b k r).chosen)
    (hj : j ∉ (greedyState A b k r).chosen) :
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
      have hknorm :
          ‖(greedyState A b k r).col (k r)‖ = 1 :=
        selected_norm_one A b ε k t r hrun hrlt
      have hiNew :
          i = k r ∨ i ∈ (greedyState A b k r).chosen := by
        simpa [greedyState, greedyStep] using hi
      have hjOld : j ∉ (greedyState A b k r).chosen := by
        intro hm
        apply hj
        have hmem : j ∈ insert (k r) (greedyState A b k r).chosen :=
          Finset.mem_insert.mpr (Or.inr hm)
        simpa [greedyState, greedyStep] using hmem
      have hjne : ¬(j = k r) := by
        intro hjEq
        apply hj
        have hmem : j ∈ insert (k r) (greedyState A b k r).chosen :=
          Finset.mem_insert.mpr (Or.inl hjEq)
        simpa [greedyState, greedyStep] using hmem
      have hcoli :
          (greedyState A b k (r + 1)).col i =
            (greedyState A b k r).col i := by
        simp [greedyState, greedyStep, hiNew]
      have hcolj :
          (greedyState A b k (r + 1)).col j =
            normalizeVec
              ((greedyState A b k r).col j -
                ⟪(greedyState A b k r).col (k r),
                  (greedyState A b k r).col j⟫_ℝ •
                  (greedyState A b k r).col (k r)) := by
        simp [greedyState, greedyStep, hjOld, hjne]
      rw [hcoli, hcolj]
      rcases hiNew with rfl | hiOld
      · exact inner_normalize_reject_self _ _ hknorm
      · exact inner_normalize_reject_of_orthogonal _ _ _
          (ih hrle hiOld hjOld) (ih hrle hiOld hknot)
