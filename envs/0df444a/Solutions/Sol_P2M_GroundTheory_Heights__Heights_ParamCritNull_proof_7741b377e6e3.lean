-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ParamCritNull_proof_7741b377e6e3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-27T05:14:33.45761+00:00
-- url     : https://prove2.me/submissions/1559cc0a-4fd6-4105-ab82-e7e6d40dbd36

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StParamCritNull
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PRankDeficientFibreInfinite
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PFibreBound
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PInjectiveHolomorphicInverse
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_HolomorphicZerosNotIsolated
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_NullZero
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PParamCritNull
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ComplexSets_FibreBound_proof_4038dff927b3
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ImplicitCurve_proof_a85e02a226ac
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_GermFiniteProjection_proof_717bd219ddcc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_HolomorphicFibreInfinite_proof_2a14330f99ea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_analyticAt_of_differentiableOn_a52ac3580ddc
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_InjectiveHolomorphicInverse_proof_0b742c511c74
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_RankDeficientFibreInfinite_proof_f29723796266
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_IndefiniteRowSideFullHecke_ComplexSets_analyticAt_det_fderiv_e2dfa5ad9526
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4
import Theorems.Thm_ReciprocityTheory_AnForm_volume_zero_set_of_analyticOnNhd


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
open MvPolynomial MeasureTheory Metric Matrix ComplexSets
namespace GroundTheory.Heights₂.Heights
namespace ParamCritNull
theorem _root_.solution : ParamCritNull.Statement := by
  intro n d W A σ r N hW hdim hA hσ hinj hN hZ
  have hg : DifferentiableOn ℂ (fun v => A *ᵥ σ v) (ball (0 : Fin d → ℂ) r) := by
    have hL : Differentiable ℂ (fun x : Fin n → ℂ => A *ᵥ x) :=
      (LinearMap.toContinuousLinearMap (Matrix.mulVecLin A)).differentiable
    exact hL.comp_differentiableOn hσ
  set Ω : Set (Fin d → ℂ) := ball (0 : Fin d → ℂ) r ∩ σ ⁻¹' N with hΩdef
  have hΩ : IsOpen Ω := hσ.continuousOn.isOpen_inter_preimage isOpen_ball hN
  rcases Set.eq_empty_or_nonempty Ω with hemp | hne
  · have hsub : {w | w ∈ ball (0 : Fin d → ℂ) r ∧ σ w ∈ N ∧
        LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) = 0} ⊆ Ω :=
      fun w hw => ⟨hw.1, hw.2.1⟩
    rw [hemp] at hsub
    rw [Set.subset_empty_iff.mp hsub, measure_empty]

  have hsome : ∃ w ∈ ball (0 : Fin d → ℂ) r,
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have hrank : ∀ v ∈ Ω, ¬ Function.Injective (fderiv ℂ (fun v => A *ᵥ σ v) v) := by
      intro v hv hinjv
      have h0 := hcon v hv.1
      rw [LinearMap.det_eq_zero_iff_ker_ne_bot] at h0
      exact h0 (LinearMap.ker_eq_bot.mpr hinjv)
    obtain ⟨y, hy⟩ := IndefiniteRowSideFullHecke.ComplexSets.RankDeficientFibreInfinite.proof d d Ω (fun v => A *ᵥ σ v) hΩ hne
      (hg.mono Set.inter_subset_left) hrank
    have himg : (σ '' {t | t ∈ Ω ∧ A *ᵥ σ t = y}).Infinite :=
      hy.image (hinj.mono fun t ht => ht.1.1)
    have hfin := (ComplexSets.FibreBound.proof n d W A hW hdim hA y).2.1
    refine himg (hfin.subset ?_)
    rintro x ⟨t, ⟨⟨htb, htN⟩, hty⟩, rfl⟩
    exact ⟨hZ t htb htN, hty⟩

  have han : AnalyticOnNhd ℂ (fun w =>
      LinearMap.det (fderiv ℂ (fun v => A *ᵥ σ v) w : (Fin d → ℂ) →ₗ[ℂ] Fin d → ℂ))
      (ball (0 : Fin d → ℂ) r) := fun w hw =>
    IndefiniteRowSideFullHecke.ComplexSets.analyticAt_det_fderiv
      (IndefiniteRowSideFullHecke.ComplexSets.InjectiveHolomorphicInverse.analyticAt_of_differentiableOn isOpen_ball hg hw)
  refine measure_mono_null ?_ (ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_ball
    (convex_ball (0 : Fin d → ℂ) r).isPreconnected han hsome)
  exact fun w hw => ⟨hw.1, hw.2.2⟩
end ParamCritNull
end GroundTheory.Heights₂.Heights
