-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_continuous_comp_torusMap_zero_f772cf319c00
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T05:28:44.076706+00:00
-- url     : https://prove2.me/submissions/e104089f-fa00-4aac-beba-a74cc432f9d0

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_torusMap_zero_mem_b866d0e1b1dd
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_continuous_torusMap


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
    {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    Continuous fun θ => G (torusMap (0 : Fin n → ℂ) (fun _ => r) θ) :=
  continuous_iff_continuousAt.2 fun θ =>
    (hd _ (torusMap_zero_mem hr0 hr1 θ).1 (torusMap_zero_mem hr0 hr1 θ).2).continuousAt.comp
      (continuous_torusMap 0 r).continuousAt
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
