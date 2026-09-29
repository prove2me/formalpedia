-- Prove2me | solution 1 for SparseApprox.Greedy.correlation_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T00:57:35.783853+00:00
-- url     : https://prove2.me/submissions/2edeb7df-74c7-4d7b-b88f-d88dc0a81e89

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

theorem aux_clb_sum_abs_le {n : ℕ} (u : EuclideanSpace ℝ (Fin n)) :
    ∑ i, |u i| ≤ Real.sqrt (nnz u) * ‖u‖ := by
  have h1 : ∑ i, |u i| = ∑ i ∈ nzSet u, |u i| := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    simp only [nzSet, Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
    simp [hi]
  have h2 : (∑ i ∈ nzSet u, |u i|) ^ 2 ≤ (nnz u : ℝ) * ‖u‖ ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq (nzSet u) (fun _ => (1:ℝ)) (fun i => |u i|)
    simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at this
    calc _ ≤ _ := this
      _ ≤ (nnz u : ℝ) * ‖u‖ ^ 2 := by
        unfold nnz
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        rw [EuclideanSpace.real_norm_sq_eq]
        apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        intros
        positivity
  rw [h1]
  have h3 : 0 ≤ ∑ i ∈ nzSet u, |u i| := Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  calc ∑ i ∈ nzSet u, |u i| = Real.sqrt ((∑ i ∈ nzSet u, |u i|) ^ 2) := (Real.sqrt_sq h3).symm
    _ ≤ Real.sqrt ((nnz u : ℝ) * ‖u‖ ^ 2) := Real.sqrt_le_sqrt h2
    _ = Real.sqrt (nnz u) * ‖u‖ := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (norm_nonneg _)]

theorem aux_clb_main {m n : ℕ} (c : Fin n → EuclideanSpace ℝ (Fin m))
    (R : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (u : EuclideanSpace ℝ (Fin n))
    (hR : ε < ‖R‖) (hu : ‖(∑ i, u i • c i) - R‖ ≤ ε / 2) :
    ∃ j : Fin n, ‖R‖ ^ 2 ≤ 2 * Real.sqrt (nnz u) * ‖u‖ * |⟪c j, R⟫_ℝ| := by
  set v := ∑ i, u i • c i with hv
  have key : ‖R‖ ^ 2 / 2 ≤ ∑ i, |u i| * |⟪c i, R⟫_ℝ| := by
    have e1 : ‖R‖ ^ 2 = ⟪R, v⟫_ℝ - ⟪R, v - R⟫_ℝ := by
      rw [inner_sub_right, real_inner_self_eq_norm_sq]; ring
    have e2 : ⟪R, v⟫_ℝ = ∑ i, u i * ⟪c i, R⟫_ℝ := by
      rw [hv, inner_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [real_inner_smul_right, real_inner_comm]
    have e3 : -⟪R, v - R⟫_ℝ ≤ ‖R‖ * (ε / 2) := by
      have h1 := abs_real_inner_le_norm R (v - R)
      have h4 := neg_abs_le ⟪R, v - R⟫_ℝ
      have h5 := mul_le_mul_of_nonneg_left hu (norm_nonneg R)
      linarith
    have e4 : ∑ i, u i * ⟪c i, R⟫_ℝ ≤ ∑ i, |u i| * |⟪c i, R⟫_ℝ| := by
      apply Finset.sum_le_sum
      intro i _
      rw [← abs_mul]
      exact le_abs_self _
    have e5 : ‖R‖ * (ε / 2) ≤ ‖R‖ ^ 2 / 2 := by nlinarith [norm_nonneg R]
    linarith
  rcases isEmpty_or_nonempty (Fin n) with hn | hn
  · exfalso
    have h0 : ∑ i, |u i| * |⟪c i, R⟫_ℝ| = 0 := by simp
    have : 0 < ‖R‖ := by linarith
    nlinarith
  · obtain ⟨j, -, hj⟩ :=
      Finset.exists_max_image Finset.univ (fun i => |⟪c i, R⟫_ℝ|) Finset.univ_nonempty
    refine ⟨j, ?_⟩
    have h6 : ∑ i, |u i| * |⟪c i, R⟫_ℝ| ≤ (∑ i, |u i|) * |⟪c j, R⟫_ℝ| := by
      rw [Finset.sum_mul]
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (hj i hi) (abs_nonneg _)
    have h7 := aux_clb_sum_abs_le u
    have h8 : (∑ i, |u i|) * |⟪c j, R⟫_ℝ| ≤ Real.sqrt (nnz u) * ‖u‖ * |⟪c j, R⟫_ℝ| :=
      mul_le_mul_of_nonneg_right h7 (abs_nonneg _)
    linarith

end SparseApprox.Greedy

open SparseApprox.Greedy
open scoped InnerProductSpace

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u) :
    ∃ j : Fin n, ‖(greedyState A b k r).res‖ ^ 2 ≤
      2 * Real.sqrt (nnz u) * ‖u‖ * |⟪(greedyState A b k r).col j, (greedyState A b k r).res⟫_ℝ| := by
  exact aux_clb_main _ _ ε hε u (hrun r hr).1 hu.1
