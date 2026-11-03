-- Prove2me | solution 1 for RegevLWE.Hyperplane.rhoLattice_poisson
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T22:27:24.41952+00:00
-- url     : https://prove2.me/submissions/a8f94b0a-d614-4787-abad-781597cdf9fb

import Mathlib
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_ZLattice_tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
import Theorems.Thm_ZLattice_summable_fourierIntegral_mul_fourierChar_dualSubmodule
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift

open MeasureTheory Filter Topology FourierTransform RegevLWE.GaussConv RegevLWE.Hyperplane
open scoped FourierTransform SchwartzMap

set_option backward.isDefEq.respectTransparency.types false

private lemma inner_nondegenerate (n : ℕ) :
    (innerₗ (EuclideanSpace ℝ (Fin n))).Nondegenerate :=
  ⟨fun x hx => inner_self_eq_zero.mp (hx x), fun x hx => inner_self_eq_zero.mp (hx x)⟩

private lemma inner_flip_eq (n : ℕ) :
    LinearMap.BilinForm.flip (innerₗ (EuclideanSpace ℝ (Fin n))) =
      innerₗ (EuclideanSpace ℝ (Fin n)) := by
  ext x y
  exact real_inner_comm x y

private lemma exists_schwartz_rho (n : ℕ) {r : ℝ} (hr : 0 < r) :
    ∃ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ x : EuclideanSpace ℝ (Fin n),
      f x = (rho r x : ℂ) := by
  obtain ⟨g, hg⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin n)
  let u : ℝˣ := Units.mk0 r⁻¹ (inv_ne_zero hr.ne')
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft u
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e g, fun x => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg, rho]
  congr 2
  have he : e x = r⁻¹ • x := rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  ring

private lemma fourier_schwartz_rho {n : ℕ} {r : ℝ} (hr : 0 < r)
    (f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ)) (hf : ∀ x, f x = (rho r x : ℂ))
    (w : EuclideanSpace ℝ (Fin n)) :
    VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
      (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) w =
      (r : ℂ) ^ n * (rho (1 / r) w : ℂ) := by
  have hfn : (⇑f : EuclideanSpace ℝ (Fin n) → ℂ) = fun x => (rhoShift r 0 x : ℂ) := by
    funext x
    rw [hf x]
    simp [rhoShift]
  have h_four := RegevLWE.GaussConv.fourier_rhoShift hr (0 : EuclideanSpace ℝ (Fin n)) w
  change VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
    (innerₗ (EuclideanSpace ℝ (Fin n))) (fun x => (rhoShift r 0 x : ℂ)) w = _ at h_four
  rw [hfn, h_four]
  simp [inner_zero_left]

theorem solution {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n)))
    [DiscreteTopology L] [IsZLattice ℝ L] {r : ℝ} (hr : 0 < r) :
    rhoLattice r L = (ZLattice.covolume L)⁻¹ * r ^ n * rhoDual (1 / r) L ∧
      (ZLattice.covolume L)⁻¹ * r ^ n ≤ rhoLattice r L := by
  obtain ⟨f, hf⟩ := exists_schwartz_rho n hr
  have h_poisson := ZLattice.tsum_translate_eq_inv_covolume_mul_tsum_fourierIntegral
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n)
    L f (0 : EuclideanSpace ℝ (Fin n))
  have h_sum := ZLattice.summable_fourierIntegral_mul_fourierChar_dualSubmodule
    MeasureTheory.volume (innerₗ (EuclideanSpace ℝ (Fin n))) (inner_nondegenerate n)
    L f (0 : EuclideanSpace ℝ (Fin n))
  rw [inner_flip_eq n] at h_poisson h_sum
  have h_lhs : (∑' x : L, f (0 + (x : EuclideanSpace ℝ (Fin n)))) = (rhoLattice r L : ℂ) := by
    unfold rhoLattice
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun x => ?_
    rw [zero_add, hf]
  have h_term : ∀ y : dual L,
      VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
        (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) (y : EuclideanSpace ℝ (Fin n)) *
        (𝐞 (innerₗ (EuclideanSpace ℝ (Fin n)) 0 (y : EuclideanSpace ℝ (Fin n))) : ℂ) =
      ((r ^ n * rho (1 / r) (y : EuclideanSpace ℝ (Fin n)) : ℝ) : ℂ) := by
    intro y
    rw [fourier_schwartz_rho hr f hf]
    simp
  have h_rhs : (∑' y : dual L,
      VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
        (innerₗ (EuclideanSpace ℝ (Fin n))) (⇑f) (y : EuclideanSpace ℝ (Fin n)) *
        (𝐞 (innerₗ (EuclideanSpace ℝ (Fin n)) 0 (y : EuclideanSpace ℝ (Fin n))) : ℂ)) =
      ((r ^ n * rhoDual (1 / r) L : ℝ) : ℂ) := by
    simp_rw [h_term]
    rw [← Complex.ofReal_tsum, tsum_mul_left]
    rfl
  rw [h_lhs, h_rhs] at h_poisson
  have h_eq : rhoLattice r L = (ZLattice.covolume L)⁻¹ * r ^ n * rhoDual (1 / r) L := by
    apply Complex.ofReal_injective
    rw [h_poisson]
    push_cast
    ring
  refine ⟨h_eq, ?_⟩
  have h_sum_real : Summable (fun y : dual L => r ^ n * rho (1 / r) (y : EuclideanSpace ℝ (Fin n))) := by
    have h_norm := h_sum.norm
    refine h_norm.congr fun y => ?_
    rw [h_term y, Complex.norm_real, Real.norm_of_nonneg (by unfold rho; positivity)]
  have h_sum_rho : Summable (fun y : dual L => rho (1 / r) (y : EuclideanSpace ℝ (Fin n))) := by
    have h_mul := h_sum_real.mul_left (r ^ n)⁻¹
    refine h_mul.congr fun y => ?_
    exact inv_mul_cancel_left₀ (pow_ne_zero n hr.ne') _
  have h_one_le : 1 ≤ rhoDual (1 / r) L := by
    unfold rhoDual
    calc (1 : ℝ)
        = rho (1 / r) ((0 : dual L) : EuclideanSpace ℝ (Fin n)) := by simp [rho]
      _ ≤ ∑' y : dual L, rho (1 / r) (y : EuclideanSpace ℝ (Fin n)) :=
          h_sum_rho.le_tsum (0 : dual L) fun y _ => by unfold rho; positivity
  have h_cov_pos : 0 < ZLattice.covolume L := ZLattice.covolume_pos L MeasureTheory.volume
  rw [h_eq]
  exact le_mul_of_one_le_right (by positivity) h_one_le
