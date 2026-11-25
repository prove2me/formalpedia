-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_PointwiseLelong_main_bound_fdf9c91e7ac8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:40:47.95498+00:00
-- url     : https://prove2.me/submissions/45c53a3b-11a6-4f8a-b075-8cee49ecf710

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_IsProbabilityMeasureSphereLaw
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerMul
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_SphereMean
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_LatticeLemmas_PPointwiseLelong
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_eval_smul_d6bde57d50a9
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_phase_bound_e8e64de5478d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_isProbabilityMeasure_phaseLaw_a2795f84d538
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_isProbabilityMeasure_sphereLaw_257e12da9c39
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereMean_eq_integral_f73535e3ca42
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_integrable_sphereLaw_eb6bacd4ac77
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_log_6df905eb445b
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_sphereIntegrable_coord_e75478f7b92c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_continuous_coordAlong_729188be789e
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_radialMap_3e0051e2cbe4
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarMap_b887a0601dcd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_PointwiseLelong_measurable_polarIntegrand_e6a977039675
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_sphereMeanLinear_a6c63502716d


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights
open MvPolynomial MeasureTheory ProbabilityTheory Real
noncomputable section
open GroundTheory.Heights₂.Heights.PointwiseLelong
variable {N : ℕ}
namespace GroundTheory.Heights₂.Heights.PointwiseLelong
theorem _root_.solution (h1 : SphereProjectionLaw.Statement) {d : ℕ} {Q : MvPolynomial (Fin N) ℂ}
    (hQ0 : Q ≠ 0) (hQ : Q.IsHomogeneous d) (p : Fin N → ℂ) (hp : ∑ j, ‖p j‖ ^ 2 = 1)
    (hQp : eval p Q ≠ 0) :
    Real.log ‖eval p Q‖ - d * (harmonic (N - 1) : ℝ) / 2 ≤
      sphereMean (HermNorm.std N) 1 (fun u ↦ Real.log ‖eval (fun j ↦ u (0, j)) Q‖) := by
  have := isProbabilityMeasure_sphereLaw (N := N)
  have := isProbabilityMeasure_phaseLaw
  have hF : Measurable fun z : Fin N → ℂ => Real.log ‖eval z Q‖ :=
    Real.measurable_log.comp (continuous_norm.comp (MvPolynomial.continuous_eval Q)).measurable
  have hFi : Integrable (fun z => Real.log ‖eval z Q‖) (sphereLaw N) :=
    integrable_sphereLaw hF (sphereIntegrable_log hQ0)
  rw [sphereMean_eq_integral hF]
  obtain ⟨hN1, hN2⟩ := h1 N p hp
  rcases Nat.lt_or_ge N 2 with hN | hN
  ·
    obtain rfl : N = 1 := by
      rcases N with _ | _ | N
      · simp at hp
      · rfl
      · omega
    have hp' : ‖p 0‖ ^ 2 = 1 := by simpa using hp
    have hae : ∀ᵐ z ∂sphereLaw 1, Real.log ‖eval z Q‖ = Real.log ‖eval p Q‖ := by
      filter_upwards [hN1 rfl] with z hz
      have hpp : star (p 0) * p 0 = 1 := by
        rw [Complex.star_def, Complex.conj_mul']
        exact_mod_cast hp'
      have hzp : z = coordAlong p z • p := by
        funext i
        rw [Subsingleton.elim i 0]
        simp only [coordAlong, Fin.sum_univ_one, Pi.smul_apply, smul_eq_mul]
        calc z 0 = z 0 * (star (p 0) * p 0) := by rw [hpp, mul_one]
          _ = _ := by ring
      rw [hzp, eval_smul hQ, norm_mul, norm_pow, hz, one_pow, one_mul]
    rw [integral_congr_ae hae, integral_const]
    simp
  · obtain ⟨hdec, hprod, hsq⟩ := hN2 hN
    have hρ := measurable_radialMap p
    have hψ := measurable_polarMap p
    have hG := measurable_polarIntegrand Q p
    have : IsProbabilityMeasure ((sphereLaw N).map (radialMap p)) :=
      Measure.isProbabilityMeasure_map hρ.aemeasurable
    have hmap : (sphereLaw N).map (polarMap p) = phaseLaw.prod ((sphereLaw N).map (radialMap p)) :=
      hprod

    have hae : (fun z => Real.log ‖eval z Q‖) =ᵐ[sphereLaw N] fun z => polarIntegrand Q p (polarMap p z) := by
      filter_upwards [hdec] with z hz
      simp only [polarIntegrand, polarMap, radialMap, Complex.norm_mul_exp_arg_mul_I]
      rw [← hz.1]
    have hGi : Integrable (polarIntegrand Q p) (phaseLaw.prod ((sphereLaw N).map (radialMap p))) := by
      rw [← hmap, integrable_map_measure hG.aestronglyMeasurable hψ.aemeasurable]
      exact hFi.congr hae
    have hint : ∫ z, Real.log ‖eval z Q‖ ∂sphereLaw N =
        ∫ y, ∫ θ, polarIntegrand Q p (θ, y) ∂phaseLaw ∂((sphereLaw N).map (radialMap p)) := by
      rw [integral_congr_ae hae, ← integral_map hψ.aemeasurable hG.aestronglyMeasurable, hmap,
        integral_prod_symm _ hGi]

    have hpos : ∀ᵐ y ∂((sphereLaw N).map (radialMap p)), 0 < y.1 := by
      have hsqm : Measurable fun z => ‖coordAlong p z‖ ^ 2 :=
        ((continuous_norm.comp (continuous_coordAlong p)).pow 2).measurable
      have h0 : ∀ᵐ x ∂((sphereLaw N).map fun z => ‖coordAlong p z‖ ^ 2), x ≠ 0 := by
        rw [hsq]
        refine (withDensity_absolutelyContinuous _ _).ae_le (?_ : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0)
        rw [ae_iff]
        simp
      have h0' := ae_of_ae_map hsqm.aemeasurable h0
      rw [ae_map_iff hρ.aemeasurable (measurableSet_lt measurable_const measurable_fst)]
      filter_upwards [h0'] with z hz
      have h2 : 0 ≤ ‖coordAlong p z‖ := norm_nonneg _
      show 0 < ‖coordAlong p z‖
      refine lt_of_le_of_ne h2 fun h => hz ?_
      rw [← h]
      simp
    have hlow : ∀ᵐ y ∂((sphereLaw N).map (radialMap p)),
        Real.log ‖eval p Q‖ + d * Real.log y.1 ≤ ∫ θ, polarIntegrand Q p (θ, y) ∂phaseLaw := by
      filter_upwards [hpos] with y hy
      have := phase_bound hQ p y.2 hQp hy (√(1 - y.1 ^ 2))
      simp only [polarIntegrand]
      exact this

    have hmc : Measurable fun z => Real.log ‖coordAlong p z‖ :=
      Real.measurable_log.comp (continuous_norm.comp (continuous_coordAlong p)).measurable
    have hml : Measurable fun y : ℝ × (Fin N → ℂ) => Real.log y.1 :=
      Real.measurable_log.comp measurable_fst
    have hlogν : Integrable (fun y : ℝ × (Fin N → ℂ) => Real.log y.1) ((sphereLaw N).map (radialMap p)) := by
      rw [integrable_map_measure hml.aestronglyMeasurable hρ.aemeasurable]
      exact integrable_sphereLaw hmc (sphereIntegrable_coord hp)
    have hmean : ∫ y, Real.log y.1 ∂((sphereLaw N).map (radialMap p)) = -(harmonic (N - 1) : ℝ) / 2 := by
      rw [integral_map hρ.aemeasurable hml.aestronglyMeasurable]
      exact (sphereMean_eq_integral hmc).symm.trans (sphereMeanLinear N p hp)
    rw [hint]
    calc Real.log ‖eval p Q‖ - d * (harmonic (N - 1) : ℝ) / 2
        = ∫ y, (Real.log ‖eval p Q‖ + d * Real.log y.1) ∂((sphereLaw N).map (radialMap p)) := by
          rw [integral_add (integrable_const _) (hlogν.const_mul _), integral_const,
            integral_const_mul, hmean]
          simp
          ring
      _ ≤ _ := integral_mono_ae ((integrable_const _).add (hlogν.const_mul _))
          hGi.integral_prod_right hlow
end GroundTheory.Heights₂.Heights.PointwiseLelong
