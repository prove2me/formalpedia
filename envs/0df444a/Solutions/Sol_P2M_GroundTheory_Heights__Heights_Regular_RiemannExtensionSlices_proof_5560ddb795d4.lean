-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_proof_5560ddb795d4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T08:35:56.237016+00:00
-- url     : https://prove2.me/submissions/97f461c8-635d-4205-8d31-e6755316f1a4

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_exists_analytic_on_ball_13d924dd686e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Regular
open Complex Metric MeasureTheory Set Filter Topology ReciprocityTheory.AnForm.Osgood
open scoped Real
noncomputable section
open RiemannExtensionSlices
namespace GroundTheory.Heights₂.Heights.Regular
namespace RiemannExtensionSlices
theorem _root_.solution : RiemannExtensionSlices.Statement := by
  intro n G hG hlim
  obtain ⟨W, hW⟩ : ∃ W : Set (Fin n → ℂ), W = {w | ∀ i, w i ≠ 0} := ⟨_, rfl⟩
  rw [← hW] at hG
  have hWo : IsOpen W := by
    rw [hW, Set.ofPred_forall]
    exact isOpen_iInter_of_finite fun i => isOpen_ne_fun (continuous_apply i) continuous_const
  have hWd : Dense W := by
    have h := dense_pi (α := fun _ : Fin n => ℂ) (s := fun _ => ({0}ᶜ : Set ℂ)) univ
      (fun i _ => dense_compl_singleton 0)
    convert h using 1
    ext z
    simp [hW]
  have hd : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ := fun ζ h1 h2 =>
    hG.differentiableAt ((isOpen_ball.inter hWo).mem_nhds ⟨h1, by rw [hW]; exact h2⟩)
  have hlimUnder : ∀ r : ℝ, ∀ Φ : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Φ (ball 0 r) →
      (∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) → Φ z = G z) →
      ∀ w ∈ ball (0 : Fin n → ℂ) r, limUnder (𝓝[W] w) G = Φ w := by
    intro r Φ hΦa hΦG w hw
    have : (𝓝[W] w).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (hWd w)
    have hev : Φ =ᶠ[𝓝[W] w] G := by
      filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (isOpen_ball.mem_nhds hw)]
        with x hxW hxb
      rw [hW] at hxW
      exact hΦG x hxb hxW
    exact (Tendsto.congr' hev ((hΦa w hw).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)).limUnder_eq
  have hrad : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∃ r : ℝ, 0 < r ∧ r < 1 ∧ z ∈ ball (0 : Fin n → ℂ) r := by
    intro z hz
    have hz1 : ‖z‖ < 1 := mem_ball_zero_iff.mp hz
    refine ⟨(‖z‖ + 1) / 2, by positivity, by linarith, mem_ball_zero_iff.mpr (by linarith)⟩
  refine ⟨fun z => limUnder (𝓝[W] z) G, fun z hz => ?_, fun z hz hzW => ?_⟩
  · obtain ⟨r, hr0, hr1, hzr⟩ := hrad z hz
    obtain ⟨Φ, hΦa, hΦG⟩ := exists_analytic_on_ball hd hlim hr0 hr1
    refine (hΦa z hzr).congr ?_
    filter_upwards [isOpen_ball.mem_nhds hzr] with w hw
    exact (hlimUnder r Φ hΦa hΦG w hw).symm
  · obtain ⟨r, hr0, hr1, hzr⟩ := hrad z hz
    obtain ⟨Φ, hΦa, hΦG⟩ := exists_analytic_on_ball hd hlim hr0 hr1
    show limUnder (𝓝[W] z) G = G z
    rw [hlimUnder r Φ hΦa hΦG z hzr, hΦG z hzr hzW]
end RiemannExtensionSlices
end GroundTheory.Heights₂.Heights.Regular
