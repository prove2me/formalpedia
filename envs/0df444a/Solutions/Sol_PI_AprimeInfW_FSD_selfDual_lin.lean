-- Prove2me | solution 1 for PI.AprimeInfW.FSD.selfDual_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:19:28.998813+00:00
-- url     : https://prove2.me/submissions/f14e5b89-6103-4516-b264-9877c4ffa71d

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GlobalSchurBounds_GeneralLinearActions_GenusMassVolumes
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ArchimedeanOrbitMeasures_FourierSD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.AprimeInfW PI.AprimeInfW.FSD
open MeasureTheory Real Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped FourierTransform RealInnerProductSpace
variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]
namespace PI.AprimeInfW.FSD
theorem _root_.solution (A : V ≃L[ℝ] V) (hA : ∀ x y, ⟪x, A y⟫ = ⟪A x, y⟫) :
    SelfDual (ENNReal.ofReal (Real.sqrt |LinearMap.det (A : V →ₗ[ℝ] V)|) • (volume : Measure V))
      (fun x y => ((𝐞 ⟪x, A y⟫ : Circle) : ℂ)) := by
  set d := LinearMap.det (A : V →ₗ[ℝ] V) with hd_def
  have hd : d ≠ 0 := (LinearEquiv.isUnit_det' A.toLinearEquiv).ne_zero
  set c := Real.sqrt |d| with hc_def
  have hc0 : 0 < c := Real.sqrt_pos.2 (abs_pos.2 hd)
  have hcc : c * c = |d| := Real.mul_self_sqrt (abs_nonneg d)
  have hcr : (ENNReal.ofReal c).toReal = c := ENNReal.toReal_ofReal hc0.le
  have hc1 : ENNReal.ofReal c ≠ 0 := (ENNReal.ofReal_pos.2 hc0).ne'
  let e : V ≃ᵐ V := A.toHomeomorph.toMeasurableEquiv
  have he : ∀ y, e y = A y := fun _ => rfl
  have hmap : (volume : Measure V).map e = ENNReal.ofReal |d⁻¹| • volume := by
    show (volume : Measure V).map (A : V →ₗ[ℝ] V) = _
    exact Measure.map_linearMap_addHaar_eq_smul_addHaar volume hd
  have hdi : (ENNReal.ofReal |d⁻¹|).toReal = |d|⁻¹ := by
    rw [ENNReal.toReal_ofReal (abs_nonneg _), abs_inv]
  refine ⟨Measure.IsAddHaarMeasure.smul (μ := (volume : Measure V)) hc1 ENNReal.ofReal_ne_top, fun Φ hc hs hI z => ?_⟩
  have hT : ∀ y, ∫ x, Φ x * ((𝐞 ⟪x, A y⟫ : Circle) : ℂ) ∂(ENNReal.ofReal c • (volume : Measure V)) =
      (c : ℂ) * 𝓕⁻ Φ (A y) := by
    intro y
    rw [integral_smul_measure, hcr, fourierInv_eq, Complex.real_smul]
    congr 1
    exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
      simp only [Circle.smul_def, smul_eq_mul]; ring)
  simp only [hT] at hI ⊢

  have hI1 : Integrable (fun y => (c : ℂ) * 𝓕⁻ Φ (A y)) volume :=
    (integrable_smul_measure hc1 ENNReal.ofReal_ne_top).1 hI
  have hI2 : Integrable (fun y => 𝓕⁻ Φ (e y)) volume := by
    have := hI1.const_mul ((c : ℂ)⁻¹)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [he]
    rw [← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast hc0.ne'), one_mul]
  have hI3 : Integrable (𝓕⁻ Φ) volume := by
    have h := (integrable_map_equiv e (𝓕⁻ Φ)).2 hI2
    rw [hmap] at h
    exact (integrable_smul_measure (by simp [hd]) ENNReal.ofReal_ne_top).1 h
  have hF : Integrable (𝓕 Φ) volume := by
    have h := hI3.comp_neg
    refine h.congr (Filter.Eventually.of_forall fun w => ?_)
    simp only [fourierInv_eq_fourier_neg, neg_neg]
  have hΦ : Integrable Φ volume := hc.integrable_of_hasCompactSupport hs
  have hinv : 𝓕⁻ (𝓕⁻ Φ) z = Φ (-z) := by
    rw [fourierInv_eq_fourier_neg]
    exact congrFun (hc.fourier_fourierInv_eq hΦ hF) (-z)

  have hout : ∫ y, (c : ℂ) * 𝓕⁻ Φ (A y) * ((𝐞 ⟪y, A z⟫ : Circle) : ℂ) ∂(volume : Measure V) =
      (c : ℂ) * (|d|⁻¹ : ℝ) * 𝓕⁻ (𝓕⁻ Φ) z := by
    have e1 : (fun y => (c : ℂ) * 𝓕⁻ Φ (A y) * ((𝐞 ⟪y, A z⟫ : Circle) : ℂ)) =
        fun y => (c : ℂ) * (((𝐞 ⟪e y, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ (e y)) := by
      funext y
      simp only [he, hA y z]
      ring
    have key : ∫ y, (c : ℂ) * (((𝐞 ⟪e y, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ (e y)) ∂(volume : Measure V) =
        ∫ u, (c : ℂ) * (((𝐞 ⟪u, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ u) ∂((volume : Measure V).map e) :=
      (integral_map_equiv e (fun u => (c : ℂ) * (((𝐞 ⟪u, z⟫ : Circle) : ℂ) * 𝓕⁻ Φ u))).symm
    rw [e1, key, hmap, integral_smul_measure, hdi, integral_const_mul, fourierInv_eq,
      Complex.real_smul]
    simp only [Circle.smul_def, smul_eq_mul]
    push_cast
    ring
  rw [integral_smul_measure, hcr, hout, hinv, Complex.real_smul]
  have : (c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hcc, ← Complex.ofReal_mul, mul_inv_cancel₀ (abs_pos.2 hd).ne',
      Complex.ofReal_one]
  calc (c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ) * Φ (-z)) = ((c : ℂ) * ((c : ℂ) * ((|d|⁻¹ : ℝ) : ℂ))) * Φ (-z) := by
        ring
    _ = Φ (-z) := by rw [this, one_mul]
end PI.AprimeInfW.FSD
