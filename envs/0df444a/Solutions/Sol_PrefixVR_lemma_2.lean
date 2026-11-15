-- Prove2me | solution 1 for PrefixVR.lemma_2
-- status  : ACCEPTED   (prove)
-- author  : @涼宮 ハルヒ
-- created : 2026-11-14T13:26:51.428254+00:00
-- url     : https://prove2.me/submissions/7e420542-1344-48d6-a2f5-a66a655bd0c9

import Definitions.Def_PrefixVR_Variation
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open scoped BigOperators InnerProductSpace
open PrefixVR

private lemma centered_le {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι : Type*} [DecidableEq ι] (A : Finset ι) (hA : A.Nonempty) (v : ι → V) (c : V) :
    ∑ i ∈ A, ‖v i - (A.card : ℝ)⁻¹ • ∑ j ∈ A, v j‖^2 ≤ ∑ i ∈ A, ‖v i-c‖^2 := by
  let a : V := (A.card : ℝ)⁻¹ • ∑ j ∈ A, v j
  have hk : (A.card : ℝ) ≠ 0 := by exact_mod_cast hA.card_pos.ne'
  have hs : ∑ i ∈ A, (v i-a) = 0 := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, ← Nat.cast_smul_eq_nsmul ℝ]
    dsimp [a]
    rw [smul_smul, mul_inv_cancel₀ hk, one_smul, sub_self]
  have cross : ∑ i ∈ A, ⟪v i-a,a-c⟫_ℝ = 0 := by rw [← sum_inner, hs, inner_zero_left]
  have heq : ∑ i ∈ A, ‖v i-c‖^2 =
      (∑ i ∈ A, ‖v i-a‖^2) + 2*(∑ i ∈ A, ⟪v i-a,a-c⟫_ℝ) + (A.card : ℝ)*‖a-c‖^2 := by
    have hv (i : ι) : v i-c = (v i-a)+(a-c) := by module
    simp_rw [hv, norm_add_sq_real]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
    simp only [Finset.sum_const, nsmul_eq_mul, ← Finset.mul_sum]
  rw [cross] at heq
  change (∑ i ∈ A, ‖v i-a‖^2) ≤ _
  nlinarith [mul_nonneg (Nat.cast_nonneg A.card : (0 : ℝ) ≤ A.card) (sq_nonneg ‖a-c‖)]

theorem solution {n d : ℕ}
    (g : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (δ : ℝ)
    (hvar : Variation g δ) (x y : EuclideanSpace ℝ (Fin d)) (A : Finset (Fin n))
    (hA : A.Nonempty) :
    (A.card : ℝ)⁻¹ * ∑ j ∈ A,
        ‖((A.card : ℝ) / n) • ((g j x - g j y) -
          (A.card : ℝ)⁻¹ • ∑ i ∈ A, (g i x - g i y))‖ ^ 2
      ≤ (A.card : ℝ) / n * δ ^ 2 * ‖x - y‖ ^ 2 ∧
    (A.card : ℝ) / n * δ ^ 2 * ‖x - y‖ ^ 2 ≤ δ ^ 2 * ‖x - y‖ ^ 2 := by
  classical
  have hk : (0 : ℝ) < A.card := by exact_mod_cast hA.card_pos
  have hkn : A.card ≤ n := by simpa using A.card_le_univ
  have hnp : 0 < n := lt_of_lt_of_le hA.card_pos hkn
  have hn : (0 : ℝ) < n := by exact_mod_cast hnp
  have hknr : (A.card : ℝ) ≤ n := by exact_mod_cast hkn
  let v : Fin n → EuclideanSpace ℝ (Fin d) := fun j => g j x-g j y
  let c := gradAvg g x-gradAvg g y
  have hcenter := centered_le A hA v c
  have hsub : ∑ i ∈ A, ‖v i-c‖^2 ≤ ∑ i, ‖v i-c‖^2 :=
    Finset.sum_le_univ_sum_of_nonneg (fun _ => sq_nonneg _)
  have hv := hvar x y
  change (n : ℝ)⁻¹ * ∑ i, ‖g i x-g i y-gradAvg g x+gradAvg g y‖^2 ≤ _ at hv
  have hrewrite (i : Fin n) : g i x-g i y-gradAvg g x+gradAvg g y = v i-c := by dsimp [v,c]; module
  simp_rw [hrewrite] at hv
  constructor
  · have hm := mul_le_mul_of_nonneg_left (hcenter.trans hsub) (by positivity : (0 : ℝ) ≤ A.card / (n : ℝ)^2)
    have hv' := mul_le_mul_of_nonneg_left hv (by positivity : (0 : ℝ) ≤ A.card / (n : ℝ))
    have hnorm : ∀ j, ‖((A.card : ℝ)/n) • (v j-(A.card : ℝ)⁻¹ • ∑ i ∈ A, v i)‖^2 =
        ((A.card : ℝ)/n)^2 * ‖v j-(A.card : ℝ)⁻¹ • ∑ i ∈ A, v i‖^2 := by
      intro j; rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    change (A.card : ℝ)⁻¹ * ∑ j ∈ A, ‖((A.card : ℝ)/n) • (v j-(A.card : ℝ)⁻¹ • ∑ i ∈ A, v i)‖^2 ≤ _
    simp_rw [hnorm]
    rw [← Finset.mul_sum]
    have hc : (A.card : ℝ)⁻¹ * (((A.card : ℝ)/n)^2 * ∑ j ∈ A, ‖v j-(A.card : ℝ)⁻¹ • ∑ i ∈ A, v i‖^2) =
        ((A.card : ℝ)/(n : ℝ)^2) * ∑ j ∈ A, ‖v j-(A.card : ℝ)⁻¹ • ∑ i ∈ A, v i‖^2 := by field_simp
    rw [hc]
    have hc' : (A.card : ℝ)/(n : ℝ)^2 * (∑ i, ‖v i-c‖^2) =
        (A.card : ℝ)/n * ((n : ℝ)⁻¹ * ∑ i, ‖v i-c‖^2) := by ring
    rw [hc'] at hm
    exact hm.trans (by simpa only [mul_assoc] using hv')
  · have hratio : (A.card : ℝ)/n ≤ 1 := (div_le_one hn).mpr hknr
    nlinarith [mul_le_mul_of_nonneg_right hratio (mul_nonneg (sq_nonneg δ) (sq_nonneg ‖x-y‖))]

#print axioms solution
