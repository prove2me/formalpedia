-- Prove2me | solution 1 for TegmarkDimensionality.laplacian_radial_profile
-- status  : ACCEPTED   (prove)
-- author  : @moona3k
-- created : 2026-10-04T02:40:55.511123+00:00
-- url     : https://prove2.me/submissions/83864351-e85d-4dd0-ad6e-528a07ffaf74

import Definitions.Def_tegmark_laplacian
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.PiL2

open Real InnerProductSpace Filter Topology Laplacian

namespace TegmarkDimensionality.RadialProfile

variable {n : ℕ}

lemma hasFDerivAt_norm {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖)
      ((1 / ‖y‖) • innerSL ℝ y) y := by
  have hs : ‖y‖ ^ 2 ≠ 0 := by positivity
  have h := (hasStrictFDerivAt_norm_sq y).hasFDerivAt.sqrt hs
  have hf : (fun z : EuclideanSpace ℝ (Fin n) => ‖z‖) =
      fun z => √(‖z‖ ^ 2) := by
    funext z
    rw [Real.sqrt_sq_eq_abs, abs_norm]
  rw [hf]
  refine h.congr_fderiv ?_
  ext v
  simp only [Real.sqrt_sq_eq_abs, abs_norm, ContinuousLinearMap.smul_apply,
    smul_eq_mul, nsmul_eq_mul]
  field_simp [norm_ne_zero_iff.mpr hy]
  norm_num

lemma hasFDerivAt_radial {g : ℝ → ℝ} (hg : Differentiable ℝ g)
    {y : EuclideanSpace ℝ (Fin n)} (hy : y ≠ 0) :
    HasFDerivAt (fun z : EuclideanSpace ℝ (Fin n) => g ‖z‖)
      ((deriv g ‖y‖ / ‖y‖) • innerSL ℝ y) y := by
  have h := (hg ‖y‖).hasDerivAt.comp_hasFDerivAt y (hasFDerivAt_norm hy)
  simpa [Function.comp_def, smul_smul, div_eq_mul_inv] using h

lemma second_deriv_radial (g : ℝ → ℝ) (hg : ContDiff ℝ 2 g)
    {x : EuclideanSpace ℝ (Fin n)} (hx : x ≠ 0)
    (v : EuclideanSpace ℝ (Fin n)) :
    iteratedFDeriv ℝ 2 (fun z : EuclideanSpace ℝ (Fin n) => g ‖z‖) x ![v, v] =
      (((deriv (deriv g) ‖x‖ * ‖x‖ - deriv g ‖x‖) / ‖x‖ ^ 2) / ‖x‖) *
          (⟪x, v⟫_ℝ * ⟪x, v⟫_ℝ) +
        (deriv g ‖x‖ / ‖x‖) * ⟪v, v⟫_ℝ := by
  let q : ℝ → ℝ := fun t => deriv g t / t
  let G : EuclideanSpace ℝ (Fin n) →
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ) :=
    fun y => q ‖y‖ • innerSL ℝ y
  have hg' : Differentiable ℝ g := hg.differentiable (by norm_num)
  have hev : fderiv ℝ (fun z : EuclideanSpace ℝ (Fin n) => g ‖z‖) =ᶠ[𝓝 x] G := by
    filter_upwards [eventually_ne_nhds hx] with y hy
    exact (hasFDerivAt_radial hg' hy).fderiv
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hq : HasDerivAt q
      ((deriv (deriv g) ‖x‖ * ‖x‖ - deriv g ‖x‖) / ‖x‖ ^ 2) ‖x‖ := by
    simpa only [q, id_eq, mul_one] using
      (hg.differentiable_deriv_two ‖x‖).hasDerivAt.fun_div
        (hasDerivAt_id ‖x‖) hnorm
  have ha : HasFDerivAt
      (fun y : EuclideanSpace ℝ (Fin n) => q ‖y‖)
      ((((deriv (deriv g) ‖x‖ * ‖x‖ - deriv g ‖x‖) / ‖x‖ ^ 2) / ‖x‖) •
        innerSL ℝ x) x := by
    have h := hq.comp_hasFDerivAt x (hasFDerivAt_norm hx)
    simpa [Function.comp_def, smul_smul, div_eq_mul_inv] using h
  have hGd := ha.smul
    (innerSL ℝ : EuclideanSpace ℝ (Fin n) →L[ℝ]
      (EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ)).hasFDerivAt
  have hi : ∀ a b : EuclideanSpace ℝ (Fin n), innerSL ℝ a b = ⟪a, b⟫_ℝ :=
    fun _ _ => rfl
  rw [iteratedFDeriv_two_apply, hev.fderiv_eq,
    show fderiv ℝ G x = _ from hGd.fderiv]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, hi, smul_eq_mul]
  dsimp [q]
  ring

end TegmarkDimensionality.RadialProfile

open TegmarkDimensionality.RadialProfile in
theorem solution (n : ℕ) (hn : 2 < n) (g : ℝ → ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ≠ 0) (hg : ContDiff ℝ 2 g) :
    Δ (fun y : EuclideanSpace ℝ (Fin n) => g (‖y‖)) x =
      deriv (deriv g) (‖x‖) + ((n : ℝ) - 1) / ‖x‖ * deriv g (‖x‖) := by
  let b := EuclideanSpace.basisFun (Fin n) ℝ
  rw [laplacian_eq_iteratedFDeriv_orthonormalBasis
    (fun y : EuclideanSpace ℝ (Fin n) => g ‖y‖) b]
  simp_rw [second_deriv_radial g hg hx]
  have h1 : ∀ i, ⟪b i, b i⟫_ℝ = 1 := fun i => by
    rw [real_inner_self_eq_norm_sq, b.orthonormal.1 i]
    norm_num
  have h2 : ∑ i, ⟪x, b i⟫_ℝ * ⟪x, b i⟫_ℝ = ‖x‖ ^ 2 := by
    have h := b.sum_inner_mul_inner x x
    simp_rw [real_inner_comm x (b _)] at h
    rw [h, real_inner_self_eq_norm_sq]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, h2]
  simp_rw [h1, mul_one]
  rw [Finset.sum_const]
  simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  field_simp [hnorm]
  ring
