-- Prove2me | solution 1 for SparseApprox.Greedy.sparsity_nonincreasing
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-29T02:35:21.47208+00:00
-- url     : https://prove2.me/submissions/591124b2-ba64-4868-9abb-8007f3fef167

import Mathlib
import Definitions.Def_SparseApprox_Greedy_Basic
import Definitions.Def_SparseApprox_Greedy_Algorithm

open scoped InnerProductSpace

namespace SparseApprox.Greedy

lemma aux_sn_normalize {m : ℕ} (v : EuclideanSpace ℝ (Fin m)) :
    normalizeVec v = 0 ∨ ‖normalizeVec v‖ = 1 := by
  unfold normalizeVec
  by_cases h : v = 0
  · left; simp [h]
  · right
    rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)]

lemma aux_sn_inner_proj {m : ℕ} (a x : EuclideanSpace ℝ (Fin m)) (ha : a = 0 ∨ ‖a‖ = 1) :
    ⟪a, x - ⟪a, x⟫_ℝ • a⟫_ℝ = 0 := by
  rcases ha with ha | ha
  · simp [ha]
  · rw [inner_sub_right, inner_smul_right, real_inner_self_eq_norm_sq, ha]; ring

lemma aux_sn_proj_contract {m : ℕ} (a x : EuclideanSpace ℝ (Fin m)) (ha : a = 0 ∨ ‖a‖ = 1) :
    ‖x - ⟪a, x⟫_ℝ • a‖ ≤ ‖x‖ := by
  rcases ha with ha | ha
  · simp [ha]
  · have h1 : ‖x - ⟪a, x⟫_ℝ • a‖ ^ 2 = ‖x‖ ^ 2 - ⟪a, x⟫_ℝ ^ 2 := by
      rw [@norm_sub_sq_real, inner_smul_right, norm_smul, ha, real_inner_comm, Real.norm_eq_abs,
        mul_one, sq_abs]
      ring
    have h2 : 0 ≤ ‖x - ⟪a, x⟫_ℝ • a‖ := norm_nonneg _
    have h3 : 0 ≤ ‖x‖ := norm_nonneg _
    nlinarith [sq_nonneg ⟪a, x⟫_ℝ]

noncomputable def aux_sn_P {m : ℕ} (a : EuclideanSpace ℝ (Fin m)) :
    EuclideanSpace ℝ (Fin m) →L[ℝ] EuclideanSpace ℝ (Fin m) :=
  ContinuousLinearMap.id ℝ _ - (innerSL ℝ a).smulRight a

lemma aux_sn_P_apply {m : ℕ} (a x : EuclideanSpace ℝ (Fin m)) :
    aux_sn_P a x = x - ⟪a, x⟫_ℝ • a := by
  simp [aux_sn_P]

def aux_sn_Inv {m n : ℕ} (s : State m n) : Prop :=
  (∀ j, s.col j = 0 ∨ ‖s.col j‖ = 1) ∧
    ∀ i ∈ s.chosen, ∀ j ∉ s.chosen, ⟪s.col i, s.col j⟫_ℝ = 0

lemma aux_sn_Inv_init {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) : aux_sn_Inv (initState A b) := by
  refine ⟨fun j => aux_sn_normalize _, ?_⟩
  intro i hi
  simp [initState] at hi

lemma aux_sn_Inv_step {m n : ℕ} (s : State m n) (k : Fin n) (h : aux_sn_Inv s) :
    aux_sn_Inv (greedyStep s k) := by
  obtain ⟨hn, ho⟩ := h
  refine ⟨?_, ?_⟩
  · intro j
    simp only [greedyStep]
    split_ifs
    · exact hn j
    · exact aux_sn_normalize _
  · intro i hi j hj
    simp only [greedyStep] at hi hj ⊢
    rw [if_pos hi, if_neg hj]
    unfold normalizeVec
    rw [inner_smul_right]
    rcases Finset.mem_insert.mp hi with hik | hi'
    · rw [hik, aux_sn_inner_proj _ _ (hn k), mul_zero]
    · have hj' : j ∉ s.chosen := fun h => hj (Finset.mem_insert_of_mem h)
      rw [inner_sub_right, inner_smul_right, ho i hi' j hj']
      by_cases hk : k ∈ s.chosen
      · rw [ho k hk j hj']; ring
      · rw [ho i hi' k hk]; ring

lemma aux_sn_Inv_state {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (k : ℕ → Fin n) : ∀ r, aux_sn_Inv (greedyState A b k r)
  | 0 => aux_sn_Inv_init A b
  | r + 1 => aux_sn_Inv_step _ _ (aux_sn_Inv_state A b k r)

lemma aux_sn_step_feas {m n : ℕ} (s : State m n) (k : Fin n) (hk : k ∉ s.chosen)
    (h : aux_sn_Inv s) (δ : ℝ) (v : EuclideanSpace ℝ (Fin n))
    (hv : ‖(∑ i, v i • s.col i) - s.res‖ ≤ δ) :
    ∃ v' : EuclideanSpace ℝ (Fin n),
      ‖(∑ i, v' i • (greedyStep s k).col i) - (greedyStep s k).res‖ ≤ δ ∧
        nnz v' ≤ nnz v := by
  obtain ⟨hn, ho⟩ := h
  have hlam : ∀ i, ∃ c : ℝ, aux_sn_P (s.col k) (s.col i) = c • (greedyStep s k).col i := by
    intro i
    simp only [greedyStep]
    by_cases hi : i ∈ insert k s.chosen
    · rw [if_pos hi]
      rcases Finset.mem_insert.mp hi with hik | hi'
      · refine ⟨1 - ⟪s.col k, s.col k⟫_ℝ, ?_⟩
        rw [hik, aux_sn_P_apply, sub_smul, one_smul]
      · refine ⟨1, ?_⟩
        rw [aux_sn_P_apply, one_smul, real_inner_comm, ho i hi' k hk, zero_smul, sub_zero]
    · rw [if_neg hi]
      refine ⟨‖aux_sn_P (s.col k) (s.col i)‖, ?_⟩
      unfold normalizeVec
      rw [← aux_sn_P_apply, smul_smul]
      by_cases h0 : ‖aux_sn_P (s.col k) (s.col i)‖ = 0
      · rw [norm_eq_zero.mp h0, smul_zero]
      · rw [mul_inv_cancel₀ h0, one_smul]
  choose lam hlam using hlam
  refine ⟨WithLp.toLp 2 (fun i => v i * lam i), ?_, ?_⟩
  · have hsum : (∑ i, (WithLp.toLp 2 (fun i => v i * lam i) : EuclideanSpace ℝ (Fin n)) i •
        (greedyStep s k).col i) = aux_sn_P (s.col k) (∑ i, v i • s.col i) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, hlam i, smul_smul]
    rw [hsum]
    have hres : (greedyStep s k).res = aux_sn_P (s.col k) s.res := by
      rw [aux_sn_P_apply]; rfl
    rw [hres, ← map_sub, aux_sn_P_apply]
    exact (aux_sn_proj_contract _ _ (hn k)).trans hv
  · apply Finset.card_le_card
    intro i hi
    simp_all [nzSet]

end SparseApprox.Greedy

open SparseApprox.Greedy
open scoped InnerProductSpace

theorem solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (b : EuclideanSpace ℝ (Fin m)) (ε : ℝ) (hε : 0 < ε) (k : ℕ → Fin n) (t : ℕ)
    (hrun : IsGreedyRun A b ε k t) (r : ℕ) (hr : r < t)
    (u₀ u u' : EuclideanSpace ℝ (Fin n))
    (hu₀ : IsMinSparseSol (greedyState A b k 0).col (greedyState A b k 0).res (ε / 2) u₀)
    (hu : IsMinSparseSol (greedyState A b k r).col (greedyState A b k r).res (ε / 2) u)
    (hu' : IsMinSparseSol (greedyState A b k (r + 1)).col (greedyState A b k (r + 1)).res
      (ε / 2) u') :
    nnz u' ≤ nnz u ∧ nnz u ≤ nnz u₀ := by
  have step : ∀ s < t, ∀ v : EuclideanSpace ℝ (Fin n),
      ‖(∑ i, v i • (greedyState A b k s).col i) - (greedyState A b k s).res‖ ≤ ε / 2 →
      ∃ v' : EuclideanSpace ℝ (Fin n),
        ‖(∑ i, v' i • (greedyState A b k (s + 1)).col i) -
          (greedyState A b k (s + 1)).res‖ ≤ ε / 2 ∧ nnz v' ≤ nnz v := by
    intro s hs v hv
    exact aux_sn_step_feas (greedyState A b k s) (k s) (hrun s hs).2.1
      (aux_sn_Inv_state A b k s) _ v hv
  constructor
  · obtain ⟨v', hv'1, hv'2⟩ := step r hr u hu.1
    exact (hu'.2 v' hv'1).trans hv'2
  · have key : ∀ s ≤ r, ∃ v : EuclideanSpace ℝ (Fin n),
        ‖(∑ i, v i • (greedyState A b k s).col i) - (greedyState A b k s).res‖ ≤ ε / 2 ∧
        nnz v ≤ nnz u₀ := by
      intro s hs
      induction s with
      | zero => exact ⟨u₀, hu₀.1, le_rfl⟩
      | succ s ih =>
        obtain ⟨v, hv1, hv2⟩ := ih (Nat.le_of_succ_le hs)
        obtain ⟨v', hv'1, hv'2⟩ := step s (by omega) v hv1
        exact ⟨v', hv'1, hv'2.trans hv2⟩
    obtain ⟨v, hv1, hv2⟩ := key r le_rfl
    exact (hu.2 v hv1).trans hv2
