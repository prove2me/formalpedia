-- Prove2me | solution 1 for RegevLWE.GaussConv.claim_3_9
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-02T21:36:13.643817+00:00
-- url     : https://prove2.me/submissions/86c323ab-bf79-4581-a73c-73f8cc4b1574

import Mathlib
import Definitions.Def_RegevLWE_GaussConv_Gaussian
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Theorems.Thm_SchwartzMap_exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq
import Theorems.Thm_RegevLWE_GaussConv_fourier_rhoShift
import Theorems.Thm_RegevLWE_GaussConv_pointwise_bound

open MeasureTheory Filter Topology FourierTransform RegevLWE.GaussConv
open scoped FourierTransform SchwartzMap

private lemma exists_schwartz_rho (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∃ f : 𝓢(EuclideanSpace ℝ (Fin n), ℂ), ∀ x : EuclideanSpace ℝ (Fin n),
      f x = (rho t x : ℂ) := by
  obtain ⟨g, hg⟩ := SchwartzMap.exists_euclideanSpace_apply_eq_exp_neg_pi_mul_norm_sq (Fin n)
  let u : ℝˣ := Units.mk0 t⁻¹ (inv_ne_zero ht.ne')
  let e : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n) :=
    ContinuousLinearEquiv.smulLeft u
  refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℝ e g, fun x => ?_⟩
  simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, hg, rho]
  congr 2
  have he : e x = t⁻¹ • x := rfl
  rw [he, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ht)]
  ring

private lemma integrable_rho (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Integrable (rho t : EuclideanSpace ℝ (Fin n) → ℝ) MeasureTheory.volume := by
  obtain ⟨f, hf⟩ := exists_schwartz_rho n ht
  have hf_int : Integrable (⇑f) MeasureTheory.volume := f.integrable
  have h_re : (rho t : EuclideanSpace ℝ (Fin n) → ℝ) = fun x => (f x).re := by
    funext x
    rw [hf x, Complex.ofReal_re]
  rw [h_re]
  exact Complex.reCLM.integrable_comp hf_int

private lemma integral_rho_eq (n : ℕ) {t : ℝ} (ht : 0 < t) :
    (∫ x : EuclideanSpace ℝ (Fin n), rho t x) = t ^ n := by
  have h_four := RegevLWE.GaussConv.fourier_rhoShift ht
    (0 : EuclideanSpace ℝ (Fin n)) (0 : EuclideanSpace ℝ (Fin n))
  change VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
    (innerₗ (EuclideanSpace ℝ (Fin n)))
    (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift t 0 x : ℂ)) 0 = _ at h_four
  have h_lhs : VectorFourier.fourierIntegral 𝐞 MeasureTheory.volume
      (innerₗ (EuclideanSpace ℝ (Fin n)))
      (fun x : EuclideanSpace ℝ (Fin n) => (rhoShift t 0 x : ℂ)) 0 =
      ((∫ x : EuclideanSpace ℝ (Fin n), rho t x : ℝ) : ℂ) := by
    rw [VectorFourier.fourierIntegral]
    simp only [map_zero, neg_zero, AddChar.map_zero_eq_one, one_smul, rhoShift, sub_zero]
    exact integral_ofReal
  have h_rhs : Complex.exp (-(2 * Real.pi * Complex.I *
      (inner ℝ (0 : EuclideanSpace ℝ (Fin n)) (0 : EuclideanSpace ℝ (Fin n)) : ℝ))) *
      (t : ℂ) ^ n * (rho (1 / t) (0 : EuclideanSpace ℝ (Fin n)) : ℂ) =
      ((t ^ n : ℝ) : ℂ) := by
    simp [rho]
  rw [h_lhs, h_rhs] at h_four
  exact Complex.ofReal_injective h_four

theorem solution {n : ℕ} (L : Submodule ℤ (EuclideanSpace ℝ (Fin n))) [DiscreteTopology L]
    [IsZLattice ℝ L] (u : EuclideanSpace ℝ (Fin n)) {r s ε : ℝ} (hr : 0 < r) (hs : 0 < s)
    (hε : 0 < ε) (hε2 : ε < 1 / 2)
    (h : smoothingParam L ε ≤ r * s / Real.sqrt (r ^ 2 + s ^ 2)) :
    statDist (Ydensity L u r s) (nu (Real.sqrt (r ^ 2 + s ^ 2))) ≤ ENNReal.ofReal (4 * ε) := by
  set t := Real.sqrt (r ^ 2 + s ^ 2)
  have ht_pos : 0 < t := Real.sqrt_pos.mpr (by positivity)
  have ht_pow_pos : 0 < t ^ n := pow_pos ht_pos n
  have h4ε_nonneg : 0 ≤ 4 * ε := by positivity
  have h_pw : ∀ x : EuclideanSpace ℝ (Fin n),
      ENNReal.ofReal |Ydensity L u r s x - nu t x| ≤
        ENNReal.ofReal (nu t x) * ENNReal.ofReal (4 * ε) := by
    intro x
    have h_bound := RegevLWE.GaussConv.pointwise_bound L u hr hs hε hε2 h x
    change |Ydensity L u r s x - nu t x| ≤ nu t x * (4 * ε) at h_bound
    rw [← ENNReal.ofReal_mul' h4ε_nonneg]
    exact ENNReal.ofReal_le_ofReal h_bound
  have h_nu_nonneg : ∀ x : EuclideanSpace ℝ (Fin n), 0 ≤ nu t x := by
    intro x
    unfold nu rho
    positivity
  have h_nu_int : Integrable (nu t : EuclideanSpace ℝ (Fin n) → ℝ) MeasureTheory.volume :=
    (integrable_rho n ht_pos).div_const (t ^ n)
  have h_nu_integral : (∫ x : EuclideanSpace ℝ (Fin n), nu t x) = 1 := by
    unfold nu
    rw [integral_div, integral_rho_eq n ht_pos, div_self ht_pow_pos.ne']
  have h_nu_lintegral : (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (nu t x)) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal h_nu_int (Eventually.of_forall h_nu_nonneg),
      h_nu_integral, ENNReal.ofReal_one]
  unfold statDist
  calc (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal |Ydensity L u r s x - nu t x|)
      ≤ ∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (nu t x) * ENNReal.ofReal (4 * ε) :=
        lintegral_mono h_pw
    _ = (∫⁻ x : EuclideanSpace ℝ (Fin n), ENNReal.ofReal (nu t x)) * ENNReal.ofReal (4 * ε) :=
        lintegral_mul_const' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (4 * ε) := by rw [h_nu_lintegral, one_mul]
