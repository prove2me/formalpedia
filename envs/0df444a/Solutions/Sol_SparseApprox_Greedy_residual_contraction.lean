-- Prove2me | solution 1 for SparseApprox.Greedy.residual_contraction
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:27:26.075886+00:00
-- url     : https://prove2.me/submissions/d2d844c2-24e7-43fa-b59a-fb574bc60491

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

lemma aux_rc_normalize_norm {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    ‖normalizeVec v‖ = 0 ∨ ‖normalizeVec v‖ = 1 := by
  unfold normalizeVec
  rw [norm_smul, norm_inv, norm_norm]
  by_cases h : ‖v‖ = 0
  · left; simp [h]
  · right; exact inv_mul_cancel₀ h

lemma aux_rc_col_norm {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (k : ℕ → Fin n) (r : ℕ) (j : Fin n) :
    ‖(greedyState A b k r).col j‖ = 0 ∨ ‖(greedyState A b k r).col j‖ = 1 := by
  induction r generalizing j with
  | zero => exact aux_rc_normalize_norm _
  | succ r ih =>
    simp only [greedyState, greedyStep]
    split_ifs
    · exact ih j
    · exact aux_rc_normalize_norm _

lemma aux_rc_inner_self_mul {m : ℕ} (a x : EuclideanSpace ℝ (Fin m))
    (ha : ‖a‖ = 0 ∨ ‖a‖ = 1) : ⟪a, x⟫_ℝ * ⟪a, a⟫_ℝ = ⟪a, x⟫_ℝ := by
  rcases ha with h | h
  · have : a = 0 := norm_eq_zero.mp h
    simp [this]
  · rw [real_inner_self_eq_norm_sq, h]; ring

lemma aux_rc_orth {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (k : ℕ → Fin n) (r : ℕ) :
    (∀ j ∈ (greedyState A b k r).chosen,
      ⟪(greedyState A b k r).col j, (greedyState A b k r).res⟫_ℝ = 0) ∧
    (∀ j ∈ (greedyState A b k r).chosen, ∀ i ∉ (greedyState A b k r).chosen,
      ⟪(greedyState A b k r).col j, (greedyState A b k r).col i⟫_ℝ = 0) := by
  induction r with
  | zero => simp [greedyState, initState]
  | succ r ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have ha := aux_rc_col_norm A b k r (k r)
    have hstep : greedyState A b k (r+1) = greedyStep (greedyState A b k r) (k r) := rfl
    rw [hstep]
    refine ⟨?_, ?_⟩
    · intro j hj
      simp only [greedyStep] at hj ⊢
      rw [if_pos hj, inner_sub_right, real_inner_smul_right]
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · rw [aux_rc_inner_self_mul _ _ ha]; ring
      · rw [ih1 j hj']
        by_cases hk : k r ∈ (greedyState A b k r).chosen
        · rw [ih1 _ hk]; ring
        · rw [ih2 j hj' _ hk]; ring
    · intro j hj i hi
      simp only [greedyStep] at hj hi ⊢
      rw [if_pos hj, if_neg hi]
      unfold normalizeVec
      rw [real_inner_smul_right, inner_sub_right, real_inner_smul_right]
      have hi' : i ∉ (greedyState A b k r).chosen := fun h => hi (Finset.mem_insert_of_mem h)
      rcases Finset.mem_insert.mp hj with rfl | hj'
      · rw [aux_rc_inner_self_mul _ _ ha]; ring
      · rw [ih2 j hj' i hi']
        by_cases hk : k r ∈ (greedyState A b k r).chosen
        · rw [ih2 _ hk i hi']; ring
        · rw [ih2 j hj' _ hk]; ring

end SparseApprox.Greedy

open SparseApprox.Greedy
open scoped InnerProductSpace

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t) (u : EuclideanSpace ℝ (Fin n))
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (ρ : ℝ) (hρ : 4 * (nnz u : ℝ) * ‖u‖ ^ 2 ≤ ρ * ‖(greedyState A b k r).res‖ ^ 2) :
    ρ * ‖(greedyState A b k (r + 1)).res‖ ^ 2 ≤ (ρ - 1) * ‖(greedyState A b k r).res‖ ^ 2 := by
  obtain ⟨hR, _hknot, _hc0, hmax⟩ := hrun r hr
  have hstep : (greedyState A b k (r+1)).res =
      (greedyState A b k r).res -
        ⟪(greedyState A b k r).col (k r), (greedyState A b k r).res⟫_ℝ •
          (greedyState A b k r).col (k r) := rfl
  rw [hstep]
  have ha := aux_rc_col_norm A b k r (k r)
  have horth := (aux_rc_orth A b k r).1
  generalize greedyState A b k r = s at hR hmax hu hρ ha horth ⊢
  generalize hadef : s.col (k r) = a at hmax ha ⊢
  generalize hcdef : ⟪a, s.res⟫_ℝ = c at hmax ⊢
  -- norm of the new residual
  have key := aux_rc_inner_self_mul a s.res ha
  rw [hcdef] at key
  have hnorm : ‖s.res - c • a‖ ^ 2 = ‖s.res‖ ^ 2 - c ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, inner_sub_left,
      inner_sub_right, inner_sub_right, real_inner_smul_left, real_inner_smul_left,
      real_inner_smul_right, real_inner_smul_right, real_inner_comm a s.res, hcdef]
    linear_combination c * key
  rw [hnorm]
  -- all inner products bounded by |c|
  have hbound : ∀ i, |⟪s.col i, s.res⟫_ℝ| ≤ |c| := by
    intro i
    by_cases hi : i ∈ s.chosen
    · rw [horth i hi, abs_zero]; exact abs_nonneg _
    · exact hmax i hi
  set R := ‖s.res‖ with hRdef
  set y : EuclideanSpace ℝ (Fin m) := ∑ i, u i • s.col i with hydef
  set P := ⟪y, s.res⟫_ℝ with hPdef
  set S := ∑ i, |u i| with hSdef
  have hR0 : 0 < R := lt_trans hε hR
  -- upper bound on P
  have h1 : P ≤ |c| * S := by
    rw [hPdef, hydef, sum_inner, hSdef, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    rw [real_inner_smul_left]
    calc u i * ⟪s.col i, s.res⟫_ℝ ≤ |u i * ⟪s.col i, s.res⟫_ℝ| := le_abs_self _
      _ = |u i| * |⟪s.col i, s.res⟫_ℝ| := abs_mul _ _
      _ ≤ |u i| * |c| := mul_le_mul_of_nonneg_left (hbound i) (abs_nonneg _)
      _ = |c| * |u i| := mul_comm _ _
  -- Cauchy-Schwarz on the support
  have h2 : S ^ 2 ≤ (nnz u : ℝ) * ‖u‖ ^ 2 := by
    have hS : S = ∑ i ∈ nzSet u, |u i| := by
      rw [hSdef, nzSet, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · rfl
      · push Not at h; rw [h, abs_zero]
    have hU : ‖u‖ ^ 2 = ∑ i ∈ nzSet u, |u i| ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq, nzSet, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      split_ifs with h
      · rw [sq_abs]
      · push Not at h; rw [h]; ring
    rw [hS, hU, nnz]
    exact sq_sum_le_card_mul_sum_sq
  -- lower bound on P
  have h3 : R ^ 2 ≤ 2 * P := by
    have hyr : ‖y - s.res‖ ≤ ε / 2 := hu.1
    have hP : P = R ^ 2 + ⟪y - s.res, s.res⟫_ℝ := by
      rw [hPdef, inner_sub_left, hRdef, real_inner_self_eq_norm_sq]; ring
    have hlow : -(‖y - s.res‖ * R) ≤ ⟪y - s.res, s.res⟫_ℝ := by
      have := abs_real_inner_le_norm (y - s.res) s.res
      rw [← hRdef] at this
      exact (abs_le.mp this).1
    have : ‖y - s.res‖ * R ≤ ε / 2 * R := mul_le_mul_of_nonneg_right hyr hR0.le
    nlinarith
  have hP0 : 0 ≤ P := by nlinarith
  have hS0 : 0 ≤ S := Finset.sum_nonneg (fun i _ => abs_nonneg (u i))
  have h4 : P ^ 2 ≤ c ^ 2 * S ^ 2 := by
    have : P ^ 2 ≤ (|c| * S) ^ 2 := pow_le_pow_left₀ hP0 h1 2
    rw [mul_pow, sq_abs] at this
    exact this
  have h5 : R ^ 2 * R ^ 2 ≤ R ^ 2 * (ρ * c ^ 2) := by
    have hc2 : 0 ≤ c ^ 2 := sq_nonneg c
    nlinarith
  have h6 : R ^ 2 ≤ ρ * c ^ 2 := le_of_mul_le_mul_left h5 (by positivity)
  nlinarith
