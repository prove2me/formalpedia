-- Prove2me | solution 1 for SAGA.StronglyConvex.lemma3_variance_bound
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:40:30.520238+00:00
-- url     : https://prove2.me/submissions/9b652ff1-75a2-4699-b8d0-01c47d0c9f06

import Mathlib
import Definitions.Def_SAGA_StronglyConvex_sagaW

set_option autoImplicit false

namespace SAGA18f1

open scoped RealInnerProductSpace

lemma sq_expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (u v w : E) :
    ‖u - v + w‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 + ‖w‖ ^ 2 - 2 * ⟪u, v⟫ + 2 * ⟪u, w⟫ - 2 * ⟪v, w⟫ := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right]
  rw [real_inner_comm v u, real_inner_comm w u, real_inner_comm w v]
  ring

lemma young_expand {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (β : ℝ)
    (a b p q : E) :
    ‖β • (a - p) + (b - q)‖ ^ 2 = β ^ 2 * ‖a‖ ^ 2 - 2 * β ^ 2 * ⟪a, p⟫ + β ^ 2 * ‖p‖ ^ 2
      + 2 * β * ⟪a, b⟫ - 2 * β * ⟪a, q⟫ - 2 * β * ⟪p, b⟫ + 2 * β * ⟪p, q⟫
      + ‖b‖ ^ 2 - 2 * ⟪b, q⟫ + ‖q‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    ← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right, inner_smul_left,
    inner_smul_right, RCLike.conj_to_real]
  rw [real_inner_comm b a, real_inner_comm p a, real_inner_comm q a, real_inner_comm q p,
    real_inner_comm q b, real_inner_comm b p]
  ring

lemma key {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} (hn : 0 < n)
    (β : ℝ) (hβ : 0 < β) (a b : Fin n → E) :
    (1 / (n : ℝ)) * ∑ j, ‖a j - b j + (1 / (n : ℝ)) • ∑ i, b i‖ ^ 2 ≤
      (1 + β⁻¹) * ((1 / (n : ℝ)) * ∑ j, ‖b j‖ ^ 2)
        + (1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖a j‖ ^ 2)
        - β * ‖(1 / (n : ℝ)) • ∑ i, a i‖ ^ 2 := by
  set A := (1 / (n : ℝ)) • ∑ i, a i with hA
  set B := (1 / (n : ℝ)) • ∑ i, b i with hB
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hsa : ∑ i, a i = (n : ℝ) • A := by
    rw [hA, smul_smul, mul_one_div_cancel hN.ne', one_smul]
  have hsb : ∑ i, b i = (n : ℝ) • B := by
    rw [hB, smul_smul, mul_one_div_cancel hN.ne', one_smul]
  have h1 : ∑ j, ‖a j - b j + B‖ ^ 2 = ∑ j, ‖a j‖ ^ 2 + ∑ j, ‖b j‖ ^ 2 + n * ‖B‖ ^ 2
      - 2 * ∑ j, ⟪a j, b j⟫ + 2 * (n * ⟪A, B⟫) - 2 * (n * ‖B‖ ^ 2) := by
    simp only [sq_expand]
    have e1 : ∑ j, ⟪a j, B⟫ = n * ⟪A, B⟫ := by
      rw [← sum_inner, hsa, real_inner_smul_left]
    have e2 : ∑ j, ⟪b j, B⟫ = n * ‖B‖ ^ 2 := by
      rw [← sum_inner, hsb, real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have h2 : 0 ≤ ∑ j, ‖β • (a j - A) + (b j - B)‖ ^ 2 :=
    Finset.sum_nonneg (fun j _ => sq_nonneg _)
  have h3 : ∑ j, ‖β • (a j - A) + (b j - B)‖ ^ 2 =
      β ^ 2 * ∑ j, ‖a j‖ ^ 2 - 2 * β ^ 2 * (n * ‖A‖ ^ 2) + n * (β ^ 2 * ‖A‖ ^ 2)
      + 2 * β * ∑ j, ⟪a j, b j⟫ - 2 * β * (n * ⟪A, B⟫) - 2 * β * (n * ⟪A, B⟫)
      + n * (2 * β * ⟪A, B⟫) + ∑ j, ‖b j‖ ^ 2 - 2 * (n * ‖B‖ ^ 2) + n * ‖B‖ ^ 2 := by
    simp only [young_expand]
    have e1 : ∑ j, ⟪a j, B⟫ = n * ⟪A, B⟫ := by
      rw [← sum_inner, hsa, real_inner_smul_left]
    have e2 : ∑ j, ⟪b j, B⟫ = n * ‖B‖ ^ 2 := by
      rw [← sum_inner, hsb, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have e3 : ∑ j, ⟪a j, A⟫ = n * ‖A‖ ^ 2 := by
      rw [← sum_inner, hsa, real_inner_smul_left, real_inner_self_eq_norm_sq]
    have e4 : ∑ j, ⟪A, b j⟫ = n * ⟪A, B⟫ := by
      rw [← inner_sum, hsb, real_inner_smul_right]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, e1, e2, e3, e4,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [h1]
  rw [h3] at h2
  set SA := ∑ j, ‖a j‖ ^ 2
  set SB := ∑ j, ‖b j‖ ^ 2
  set SAB := ∑ j, ⟪a j, b j⟫
  set K := β ^ 2 * SA - 2 * β ^ 2 * (n * ‖A‖ ^ 2) + n * (β ^ 2 * ‖A‖ ^ 2)
      + 2 * β * SAB - 2 * β * (n * ⟪A, B⟫) - 2 * β * (n * ⟪A, B⟫)
      + n * (2 * β * ⟪A, B⟫) + SB - 2 * (n * ‖B‖ ^ 2) + n * ‖B‖ ^ 2 with hK
  have hQ := sq_nonneg ‖B‖
  have hid : (1 + β⁻¹) * ((1 / (n : ℝ)) * SB) + (1 + β) * ((1 / (n : ℝ)) * SA) - β * ‖A‖ ^ 2
      - (1 / (n : ℝ)) * (SA + SB + n * ‖B‖ ^ 2 - 2 * SAB + 2 * (n * ⟪A, B⟫) - 2 * (n * ‖B‖ ^ 2))
      = (1 / (n : ℝ)) * (β⁻¹ * K + n * ‖B‖ ^ 2 + n * ‖B‖ ^ 2 * β⁻¹) := by
    rw [hK]; field_simp; ring
  have hnn : 0 ≤ (1 / (n : ℝ)) * (β⁻¹ * K + n * ‖B‖ ^ 2 + n * ‖B‖ ^ 2 * β⁻¹) := by
    have := inv_pos.mpr hβ
    positivity
  linarith

end SAGA18f1

open SAGA.StronglyConvex in
theorem solution {d n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (γ β : ℝ) (hβ : 0 < β)
    (φ : Fin n → EuclideanSpace ℝ (Fin d)) (xs x : EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ j, ‖sagaW f' γ x φ j - x + γ • ((1 / (n : ℝ)) • ∑ i, f' i xs)‖ ^ 2 ≤
      γ ^ 2 * (1 + β⁻¹) * ((1 / (n : ℝ)) * ∑ j, ‖f' j (φ j) - f' j xs‖ ^ 2)
        + γ ^ 2 * (1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖f' j x - f' j xs‖ ^ 2)
        - γ ^ 2 * β * ‖(1 / (n : ℝ)) • ∑ i, f' i x - (1 / (n : ℝ)) • ∑ i, f' i xs‖ ^ 2 := by
  have hk := SAGA18f1.key hn β hβ (fun j => f' j x - f' j xs) (fun j => f' j (φ j) - f' j xs)
  rw [Finset.sum_sub_distrib, smul_sub] at hk
  have hA : (1 / (n : ℝ)) • ∑ i, (f' i x - f' i xs)
      = (1 / (n : ℝ)) • ∑ i, f' i x - (1 / (n : ℝ)) • ∑ i, f' i xs := by
    rw [Finset.sum_sub_distrib, smul_sub]
  rw [hA] at hk
  have hw : ∀ j, sagaW f' γ x φ j - x + γ • ((1 / (n : ℝ)) • ∑ i, f' i xs)
      = (-γ) • (f' j x - f' j xs - (f' j (φ j) - f' j xs)
          + ((1 / (n : ℝ)) • ∑ i, f' i (φ i) - (1 / (n : ℝ)) • ∑ i, f' i xs)) := by
    intro j
    unfold sagaW
    module
  have hn2 : ∀ j, ‖sagaW f' γ x φ j - x + γ • ((1 / (n : ℝ)) • ∑ i, f' i xs)‖ ^ 2
      = γ ^ 2 * ‖f' j x - f' j xs - (f' j (φ j) - f' j xs)
          + ((1 / (n : ℝ)) • ∑ i, f' i (φ i) - (1 / (n : ℝ)) • ∑ i, f' i xs)‖ ^ 2 := by
    intro j
    rw [hw, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, neg_sq]
  simp_rw [hn2]
  rw [← Finset.mul_sum]
  have := mul_le_mul_of_nonneg_left hk (sq_nonneg γ)
  exact le_trans (le_of_eq (by ring)) (this.trans (le_of_eq (by ring)))
