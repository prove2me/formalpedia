-- Prove2me | solution 1 for SAGA.Convex.delta_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-05T11:26:53.770772+00:00
-- url     : https://prove2.me/submissions/573d1da9-03a7-425d-aab4-a6c22b286cf4

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_sagaStep

set_option autoImplicit false

namespace SAGAHelp0acebf67

lemma young {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (a b : E) {β : ℝ}
    (hβ : 0 < β) :
    ‖a - b‖ ^ 2 ≤ (1 + β) * ‖a‖ ^ 2 + (1 + β⁻¹) * ‖b‖ ^ 2 := by
  rw [norm_sub_sq_real]
  have h1 : -(2 * inner ℝ a b) ≤ 2 * (‖a‖ * ‖b‖) := by
    have := abs_real_inner_le_norm a b
    linarith [neg_abs_le (inner ℝ a b)]
  have h2 : 2 * (‖a‖ * ‖b‖) ≤ β * ‖a‖ ^ 2 + β⁻¹ * ‖b‖ ^ 2 := by
    have hb : 0 < β⁻¹ := inv_pos.mpr hβ
    have h0 : 0 ≤ β⁻¹ * (β * ‖a‖ - ‖b‖) ^ 2 := by positivity
    have e : β⁻¹ * (β * ‖a‖ - ‖b‖) ^ 2
        = β * ‖a‖ ^ 2 - 2 * (‖a‖ * ‖b‖) + β⁻¹ * ‖b‖ ^ 2 := by
      field_simp; ring
    linarith
  nlinarith

lemma var_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] {n : ℕ} (hn : 0 < n)
    (y : Fin n → E) :
    ∑ j, ‖y j - (1 / (n : ℝ)) • ∑ i, y i‖ ^ 2 ≤ ∑ j, ‖y j‖ ^ 2 := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  set m := (1 / (n : ℝ)) • ∑ i, y i with hm
  have hsum : ∑ i, y i = (n : ℝ) • m := by
    rw [hm, smul_smul, mul_one_div_cancel hn', one_smul]
  have h : ∑ j, ‖y j - m‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 - (n : ℝ) * ‖m‖ ^ 2 := by
    simp_rw [norm_sub_sq_real]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← sum_inner, hsum,
      real_inner_smul_left, real_inner_self_eq_norm_sq]
    simp
    ring
  rw [h]
  have : 0 ≤ (n : ℝ) * ‖m‖ ^ 2 := by positivity
  linarith

end SAGAHelp0acebf67

open SAGA.Convex in
theorem solution {d n : ℕ} (hn : 0 < n)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    {γ β : ℝ} (hγ : 0 < γ) (hβ : 0 < β)
    (s : EuclideanSpace ℝ (Fin d) × (Fin n → EuclideanSpace ℝ (Fin d)))
    (xs : EuclideanSpace ℝ (Fin d)) :
    (1 / (n : ℝ)) * ∑ j, ‖sagaDelta f' γ s j‖ ^ 2 ≤
      (1 + β⁻¹) * ((1 / (n : ℝ)) * ∑ j, ‖f' j (s.2 j) - f' j xs‖ ^ 2)
        + (1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖f' j s.1 - f' j xs‖ ^ 2) := by
  set y : Fin n → EuclideanSpace ℝ (Fin d) :=
    fun j => (f' j s.1 - f' j xs) - (f' j (s.2 j) - f' j xs) with hy
  have hγ' : γ ≠ 0 := hγ.ne'
  have key : ∀ j, sagaDelta f' γ s j = y j - (1 / (n : ℝ)) • ∑ i, y i := by
    intro j
    simp only [hy, sub_sub_sub_cancel_right]
    unfold sagaDelta sagaW gradAvg
    rw [sub_sub_cancel_left, smul_neg, neg_smul, neg_neg, smul_smul, one_div γ,
      inv_mul_cancel₀ hγ', one_smul, Finset.sum_sub_distrib, smul_sub]
    abel
  have hn0 : 0 ≤ 1 / (n : ℝ) := by positivity
  calc (1 / (n : ℝ)) * ∑ j, ‖sagaDelta f' γ s j‖ ^ 2
      = (1 / (n : ℝ)) * ∑ j, ‖y j - (1 / (n : ℝ)) • ∑ i, y i‖ ^ 2 := by
        simp only [key]
    _ ≤ (1 / (n : ℝ)) * ∑ j, ‖y j‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (SAGAHelp0acebf67.var_le hn y) hn0
    _ ≤ (1 / (n : ℝ)) * ∑ j, ((1 + β) * ‖f' j s.1 - f' j xs‖ ^ 2
          + (1 + β⁻¹) * ‖f' j (s.2 j) - f' j xs‖ ^ 2) := by
        apply mul_le_mul_of_nonneg_left _ hn0
        apply Finset.sum_le_sum
        intro j _
        exact SAGAHelp0acebf67.young _ _ hβ
    _ = (1 + β⁻¹) * ((1 / (n : ℝ)) * ∑ j, ‖f' j (s.2 j) - f' j xs‖ ^ 2)
        + (1 + β) * ((1 / (n : ℝ)) * ∑ j, ‖f' j s.1 - f' j xs‖ ^ 2) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
        ring
