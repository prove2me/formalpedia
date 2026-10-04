-- Prove2me | solution 1 for TegmarkDimensionality.greens_function_harmonic
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T01:10:14.237985+00:00
-- url     : https://prove2.me/submissions/2417207e-2416-4986-9a57-682b9baa7e46

import Definitions.Def_tegmark_laplacian
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Real InnerProductSpace Filter Topology

namespace TegmarkDimensionality.GreensHarmonic

variable {n : ℕ}

lemma norm_rpow_eq (p : ℝ) (y : EuclideanSpace ℝ (Fin n)) :
    ‖y‖ ^ p = (‖y‖ ^ 2) ^ (p / 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg y)]
  congr 1
  push_cast
  ring

lemma hasFDerivAt_norm_rpow' (p : ℝ) {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ p)
      ((p * (‖y‖ ^ 2) ^ (p / 2 - 1)) • innerSL ℝ y) y := by
  have hs : (‖y‖ ^ 2) ≠ 0 := by positivity
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.rpow_const (p := p / 2) (Or.inl hs)
  have hf : (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ p) =
      fun z => (‖z‖ ^ 2) ^ (p / 2) := funext (norm_rpow_eq p)
  rw [hf]
  refine h.congr_fderiv ?_
  rw [two_nsmul, smul_add, ← add_smul]
  congr 1
  ring

lemma second_deriv (p : ℝ) {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2 (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ p) x ![v, v] =
      p * (‖x‖ ^ 2) ^ (p / 2 - 1) * ⟪v, v⟫_ℝ +
        p * ((p / 2 - 1) * (‖x‖ ^ 2) ^ (p / 2 - 1 - 1)) * 2 * (⟪x, v⟫_ℝ * ⟪x, v⟫_ℝ) := by
  set G : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun y => (p * (‖y‖ ^ 2) ^ (p / 2 - 1)) • innerSL ℝ y with hG
  have hev : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖ ^ p) =ᶠ[𝓝 x] G := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (hasFDerivAt_norm_rpow' p hy).fderiv
  have hs : (‖x‖ ^ 2) ≠ 0 := by positivity
  have hc := ((hasStrictFDerivAt_norm_sq x).hasFDerivAt.rpow_const
    (p := p / 2 - 1) (Or.inl hs)).const_mul p
  have hGd := hc.smul (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ] _).hasFDerivAt
  have hi : ∀ a b : EuclideanSpace ℝ (Fin n), innerSL ℝ a b = ⟪a, b⟫_ℝ := fun _ _ => rfl
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq, show fderiv ℝ G x = _ from hGd.fderiv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, hi, smul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

end TegmarkDimensionality.GreensHarmonic

open TegmarkDimensionality.GreensHarmonic in
theorem solution (n : ℕ) (hn : 2 < n) (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) :
    TegmarkDimensionality.laplacian (fun y => ‖y‖ ^ ((2 : ℝ) - n)) x = 0 := by
  set b := EuclideanSpace.basisFun (Fin n) ℝ
  have hb : ∀ i, EuclideanSpace.single i (1 : ℝ) = b i := fun i => by
    simp [b, EuclideanSpace.basisFun_apply]
  unfold TegmarkDimensionality.laplacian
  simp_rw [hb, second_deriv _ hx]
  have h1 : ∀ i, ⟪b i, b i⟫_ℝ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]; norm_num
  have h2 : ∑ i, ⟪x, b i⟫_ℝ * ⟪x, b i⟫_ℝ = ‖x‖ ^ 2 := by
    have := b.sum_inner_mul_inner x x
    simp_rw [real_inner_comm x (b _)] at this
    rw [this, real_inner_self_eq_norm_sq]
  simp_rw [h1, mul_one]
  rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.mul_sum, h2]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hs : 0 < ‖x‖ ^ 2 := by have := norm_pos_iff.mpr hx; positivity
  have hpow : ((‖x‖ ^ 2) ^ (((2 : ℝ) - n) / 2 - 1 - 1)) * ‖x‖ ^ 2 =
      (‖x‖ ^ 2) ^ (((2 : ℝ) - n) / 2 - 1) := by
    rw [Real.rpow_sub_one hs.ne']
    field_simp
  linear_combination (((2 : ℝ) - n) * (((2 : ℝ) - n) / 2 - 1)) * 2 * hpow
