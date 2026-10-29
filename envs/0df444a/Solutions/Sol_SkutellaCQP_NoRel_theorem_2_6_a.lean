-- Prove2me | solution 1 for SkutellaCQP.NoRel.theorem_2_6_a
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-10-28T20:34:01.142432+00:00
-- url     : https://prove2.me/submissions/55c9e3f7-8423-4ca6-82fc-9fe6192eb527

import Mathlib
import Definitions.Def_SkutellaCQP_NoRel_Setting
import Theorems.Thm_SkutellaCQP_NoRel_zqp_eq_zcqp_add

open SkutellaCQP.NoRel
open Finset Matrix

private lemma prec_irrefl {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) (j : Fin n) : ¬ prec p w i j j := by
  intro h
  rcases h with h | ⟨_, h⟩
  · exact lt_irrefl _ h
  · exact lt_irrefl _ h

private lemma prec_asym {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) {j k : Fin n} (h : prec p w i k j) : ¬ prec p w i j k := by
  intro h'
  rcases h with h1 | ⟨h1, h2⟩ <;> rcases h' with h3 | ⟨h3, h4⟩
  · linarith
  · linarith
  · linarith
  · exact lt_asymm h2 h4

private lemma Dmat_same_machine {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (i : Fin m) (j k : Fin n) :
    Dmat p w (i, j) (i, k) =
      (if prec p w i k j then w j * p i k else 0) +
        (if prec p w i j k then w k * p i j else 0) := by
  unfold Dmat
  simp only [ne_eq, not_true_eq_false, false_or]
  by_cases hjk : j = k
  · subst hjk
    simp [prec_irrefl]
  · simp only [hjk, ↓reduceIte]
    by_cases h1 : prec p w i k j
    · have h2 : ¬ prec p w i j k := prec_asym p w i h1
      simp [h1, h2]
    · simp [h1]

private lemma lemma_2_2_aux {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (μ : (Fin n → Fin m) → ℝ) (j : Fin n) :
    E μ (fun σ => SkutellaCQP.NoRel.compl p w σ j) =
      ∑ i, ((∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i), μ σ) * p i j +
        ∑ k ∈ univ.filter (fun k => prec p w i k j),
          (∑ σ ∈ univ.filter (fun σ : Fin n → Fin m => σ j = i ∧ σ k = i), μ σ) * p i k) := by
  dsimp only [E, SkutellaCQP.NoRel.compl]
  have h1 :
      (∑ σ : Fin n → Fin m,
          μ σ * (p (σ j) j + ∑ k ∈ univ.filter (fun k => prec p w (σ j) k j ∧ σ k = σ j), p (σ j) k)) =
        ∑ σ : Fin n → Fin m, ∑ i : Fin m,
          if σ j = i then
            μ σ * (p i j + ∑ k ∈ univ.filter (fun k => prec p w i k j), if σ k = i then p i k else 0)
          else 0 := by
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.sum_ite_eq univ (σ j)]
    simp only [Finset.mem_univ, ↓reduceIte]
    congr 2
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h1 : prec p w (σ j) k j <;> by_cases h2 : σ k = σ j <;> simp [h1, h2]
  rw [h1, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 :
      (∑ σ : Fin n → Fin m,
          if σ j = i then
            μ σ * (p i j + ∑ k ∈ univ.filter (fun k => prec p w i k j), if σ k = i then p i k else 0)
          else 0) =
        (∑ σ : Fin n → Fin m, if σ j = i then μ σ * p i j else 0) +
          ∑ σ : Fin n → Fin m,
            ∑ k ∈ univ.filter (fun k => prec p w i k j),
              if σ j = i ∧ σ k = i then μ σ * p i k else 0 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    by_cases hσj : σ j = i
    · simp only [hσj, ↓reduceIte, true_and, mul_add, Finset.mul_sum, mul_ite, mul_zero]
    · simp only [hσj, ↓reduceIte, false_and, Finset.sum_const_zero, add_zero]
  rw [h2]
  congr 1
  · rw [← Finset.sum_filter, Finset.sum_mul]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, Finset.sum_mul]

private lemma theorem_2_1_aux {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (a : Fin m → Fin n → ℝ)
    (μ : (Fin n → Fin m) → ℝ) (hμ : IsPairwiseRounding a μ) :
    E μ (SkutellaCQP.NoRel.val p w) = ZQP p w a := by
  have hE_val :
      E μ (SkutellaCQP.NoRel.val p w) =
        ∑ j, w j * E μ (fun σ => SkutellaCQP.NoRel.compl p w σ j) := by
    dsimp only [E, SkutellaCQP.NoRel.val]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun σ _ => by ring
  rw [hE_val]
  have hE_compl :
      ∀ j : Fin n,
        E μ (fun σ => SkutellaCQP.NoRel.compl p w σ j) =
          ∑ i : Fin m,
            (a i j * p i j +
              ∑ k ∈ univ.filter (fun k => prec p w i k j), a i j * a i k * p i k) := by
    intro j
    rw [lemma_2_2_aux]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hμ.2.2.1 j i]
    congr 1
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.mem_filter] at hk
    have hjk : j ≠ k := by
      rintro rfl
      exact prec_irrefl p w i j hk.2
    rw [hμ.2.2.2 j k hjk i i]
  simp_rw [hE_compl, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  unfold ZQP
  congr 1
  · dsimp only [cvec, SkutellaCQP.NoRel.vec, dotProduct]
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine Finset.sum_congr rfl fun i _ => by ring
  · dsimp only [SkutellaCQP.NoRel.vec, dotProduct, Matrix.mulVec]
    simp_rw [Fintype.sum_prod_type]
    have hD :
        (∑ i : Fin m, ∑ j : Fin n,
            a i j * ∑ h : Fin m, ∑ k : Fin n, Dmat p w (i, j) (h, k) * a h k) =
          ∑ i : Fin m, ∑ j : Fin n,
            a i j * ∑ k : Fin n, Dmat p w (i, j) (i, k) * a i k := by
      refine Finset.sum_congr rfl fun i _ => ?_
      refine Finset.sum_congr rfl fun j _ => ?_
      congr 1
      rw [Finset.sum_eq_single i]
      · intro h _ hne
        refine Finset.sum_eq_zero fun k _ => ?_
        unfold Dmat
        simp [Ne.symm hne]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    rw [hD]
    have hquad :
        ∀ i : Fin m,
          (∑ j : Fin n, a i j * ∑ k : Fin n, Dmat p w (i, j) (i, k) * a i k) =
            2 * ∑ j : Fin n, w j * ∑ k ∈ univ.filter (fun k => prec p w i k j),
              a i j * a i k * p i k := by
      intro i
      have lhs_eq :
          (∑ j : Fin n, a i j * ∑ k : Fin n, Dmat p w (i, j) (i, k) * a i k) =
            (∑ j : Fin n, ∑ k : Fin n,
                a i j * ((if prec p w i k j then w j * p i k else 0) * a i k)) +
              (∑ j : Fin n, ∑ k : Fin n,
                a i j * ((if prec p w i j k then w k * p i j else 0) * a i k)) := by
        simp_rw [Finset.mul_sum]
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Dmat_same_machine]
        ring
      rw [lhs_eq]
      have hswap :
          (∑ j : Fin n, ∑ k : Fin n,
              a i j * ((if prec p w i j k then w k * p i j else 0) * a i k)) =
            ∑ j : Fin n, ∑ k : Fin n,
              a i j * ((if prec p w i k j then w j * p i k else 0) * a i k) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun j _ => ?_
        refine Finset.sum_congr rfl fun k _ => ?_
        by_cases h : prec p w i k j <;> simp [h] <;> ring
      rw [hswap, ← two_mul]
      congr 1
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Finset.sum_filter, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      by_cases h : prec p w i k j <;> simp [h] <;> ring
    simp_rw [hquad]
    rw [← Finset.mul_sum, Finset.sum_comm]
    ring

private lemma zqp_le_zcqp_add {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j) (a : Fin m → Fin n → ℝ) :
    ZQP p w a ≤ ZCQP p w a + (1 / 2) * (cvec p w ⬝ᵥ SkutellaCQP.NoRel.vec a) := by
  rw [zqp_eq_zcqp_add p w a]
  have hdiag :
      0 ≤ SkutellaCQP.NoRel.vec a ⬝ᵥ (Matrix.diagonal (cvec p w) *ᵥ SkutellaCQP.NoRel.vec a) := by
    dsimp only [dotProduct, Matrix.mulVec, SkutellaCQP.NoRel.vec]
    refine Finset.sum_nonneg fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq]
      dsimp only [cvec]
      have hwx : 0 ≤ w x.2 := hw x.2
      have hpx : 0 ≤ p x.1 x.2 := le_of_lt (hp x.1 x.2)
      nlinarith [sq_nonneg (a x.1 x.2), mul_nonneg hwx hpx]
    · intro y _ hyx
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hyx), zero_mul]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  linarith

private lemma half_cvec_le_zcqp {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) (ha : Feasible a) :
    (1 / 2) * (cvec p w ⬝ᵥ SkutellaCQP.NoRel.vec a) ≤ ZCQP p w a := by
  unfold ZCQP
  have hquad :
      0 ≤ SkutellaCQP.NoRel.vec a ⬝ᵥ
        ((Dmat p w + Matrix.diagonal (cvec p w)) *ᵥ SkutellaCQP.NoRel.vec a) := by
    dsimp only [dotProduct, Matrix.mulVec, SkutellaCQP.NoRel.vec]
    refine Finset.sum_nonneg fun x _ => ?_
    refine mul_nonneg (ha.2 x.1 x.2) (Finset.sum_nonneg fun y _ => ?_)
    refine mul_nonneg ?_ (ha.2 y.1 y.2)
    simp only [Matrix.add_apply]
    refine add_nonneg ?_ ?_
    · unfold Dmat
      split_ifs with h1 h2 h3
      · exact le_rfl
      · exact mul_nonneg (hw x.2) (le_of_lt (hp x.1 y.2))
      · exact mul_nonneg (hw y.2) (le_of_lt (hp x.1 x.2))
      · exact le_rfl
    · rw [Matrix.diagonal_apply]
      dsimp only [cvec]
      split_ifs
      · exact mul_nonneg (hw x.2) (le_of_lt (hp x.1 x.2))
      · exact le_rfl
  linarith

private lemma feasible_ind {m n : ℕ} (σ : Fin n → Fin m) : Feasible (ind σ) := by
  refine ⟨fun j => ?_, fun i j => ?_⟩
  · unfold ind
    simp
  · unfold ind
    split_ifs <;> linarith

private lemma isPairwiseRounding_ind {m n : ℕ} (σ : Fin n → Fin m) :
    IsPairwiseRounding (ind σ) (fun τ => if τ = σ then 1 else 0) := by
  refine ⟨fun τ => by dsimp; split_ifs <;> linarith, by simp, fun j i => ?_, fun j k _ i h => ?_⟩
  · rw [Finset.sum_filter]
    have :
        (∑ τ : Fin n → Fin m, if τ j = i then if τ = σ then (1 : ℝ) else 0 else 0) =
          ∑ τ : Fin n → Fin m, if τ = σ then (if σ j = i then 1 else 0) else 0 := by
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases hτ : τ = σ
      · subst hτ; simp
      · simp [hτ]
    rw [this, Finset.sum_ite_eq' univ σ]
    simp [ind]
  · rw [Finset.sum_filter]
    have :
        (∑ τ : Fin n → Fin m, if τ j = i ∧ τ k = h then if τ = σ then (1 : ℝ) else 0 else 0) =
          ∑ τ : Fin n → Fin m, if τ = σ then (if σ j = i ∧ σ k = h then 1 else 0) else 0 := by
      refine Finset.sum_congr rfl fun τ _ => ?_
      by_cases hτ : τ = σ
      · subst hτ; simp
      · simp [hτ]
    rw [this, Finset.sum_ite_eq' univ σ]
    simp only [Finset.mem_univ, ↓reduceIte, ind]
    by_cases h1 : σ j = i <;> by_cases h2 : σ k = h <;> simp [h1, h2]

private lemma zcqp_ind_eq_val {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (σ : Fin n → Fin m) : ZCQP p w (ind σ) = SkutellaCQP.NoRel.val p w σ := by
  have h1 := theorem_2_1_aux p w (ind σ) (fun τ => if τ = σ then 1 else 0) (isPairwiseRounding_ind σ)
  have hE :
      E (fun τ => if τ = σ then 1 else 0) (SkutellaCQP.NoRel.val p w) =
        SkutellaCQP.NoRel.val p w σ := by
    dsimp only [E]
    simp
  rw [hE] at h1
  rw [h1, zqp_eq_zcqp_add p w (ind σ)]
  have hdiag :
      SkutellaCQP.NoRel.vec (ind σ) ⬝ᵥ
          (Matrix.diagonal (cvec p w) *ᵥ SkutellaCQP.NoRel.vec (ind σ)) =
        cvec p w ⬝ᵥ SkutellaCQP.NoRel.vec (ind σ) := by
    dsimp only [dotProduct, Matrix.mulVec, SkutellaCQP.NoRel.vec, ind]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single x]
    · rw [Matrix.diagonal_apply_eq]
      dsimp only [cvec]
      by_cases h : σ x.2 = x.1 <;> simp [h]
    · intro y _ hyx
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hyx), zero_mul]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  linarith

theorem solution {m n : ℕ} (p : Fin m → Fin n → ℝ) (w : Fin n → ℝ)
    (hp : ∀ i j, 0 < p i j) (hw : ∀ j, 0 ≤ w j)
    (a : Fin m → Fin n → ℝ) (ha : Feasible a)
    (hopt : ∀ b : Fin m → Fin n → ℝ, Feasible b → ZCQP p w a ≤ ZCQP p w b)
    (μ : (Fin n → Fin m) → ℝ) (hμ : IsPairwiseRounding a μ) :
    ∀ σ : Fin n → Fin m, E μ (SkutellaCQP.NoRel.val p w) ≤ 2 * SkutellaCQP.NoRel.val p w σ := by
  intro σ
  rw [theorem_2_1_aux p w a μ hμ, ← zcqp_ind_eq_val p w σ]
  have h1 := zqp_le_zcqp_add p w hp hw a
  have h2 := half_cvec_le_zcqp p w hp hw a ha
  have h3 := hopt (ind σ) (feasible_ind σ)
  linarith
