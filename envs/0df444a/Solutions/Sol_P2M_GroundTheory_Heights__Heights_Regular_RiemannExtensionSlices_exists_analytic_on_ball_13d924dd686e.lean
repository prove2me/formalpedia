-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_exists_analytic_on_ball_13d924dd686e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:26:41.300917+00:00
-- url     : https://prove2.me/submissions/ade2a412-6b6d-4541-9645-f880e30801df

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_continuous_comp_torusMap_zero_f772cf319c00
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_cauchy_torus_off_axes_2daaebd2de5c
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_fctl_kern_3e5189bc629a
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_kern_analyticAt_of_mem_f25be706a099

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
open GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
namespace GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
theorem _root_.solution {n : ℕ} {G : (Fin n → ℂ) → ℂ}
    (hd : ∀ ζ ∈ ball (0 : Fin n → ℂ) 1, (∀ i, ζ i ≠ 0) → DifferentiableAt ℂ G ζ)
    (hlim : ∀ z ∈ ball (0 : Fin n → ℂ) 1, ∀ i : Fin n, (∀ j, j ≠ i → z j ≠ 0) →
      ∃ c : ℂ, Tendsto (fun x : ℂ => G (Function.update z i x)) (𝓝[≠] 0) (𝓝 c))
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ Φ : (Fin n → ℂ) → ℂ, AnalyticOnNhd ℂ Φ (ball 0 r) ∧
      ∀ z ∈ ball (0 : Fin n → ℂ) r, (∀ i, z i ≠ 0) → Φ z = G z := by
  set L := torusFunctional 0 r G (continuous_comp_torusMap_zero hd hr0 hr1)
  have hne : (2 * π * I : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by simp [Real.pi_ne_zero, I_ne_zero])
  refine ⟨fun z => ((2 * π * I : ℂ) ^ n)⁻¹ * L (kern 0 r z), fun z hz =>
    analyticAt_const.mul ((L.analyticAt _).comp (kern_analyticAt_of_mem 0 hr0 hz)), fun z hz hzW => ?_⟩
  show ((2 * π * I : ℂ) ^ n)⁻¹ * fctl 0 r G (kern 0 r z) = G z
  rw [fctl_kern hr0 G hz, cauchy_torus_off_axes n G hd hlim r hr0 hr1 z hz hzW, ← mul_assoc,
    inv_mul_cancel₀ hne, one_mul]
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
