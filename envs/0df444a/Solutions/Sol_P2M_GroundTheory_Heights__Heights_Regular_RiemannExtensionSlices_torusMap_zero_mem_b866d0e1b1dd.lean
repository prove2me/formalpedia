-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_RiemannExtensionSlices_torusMap_zero_mem_b866d0e1b1dd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T04:49:30.055255+00:00
-- url     : https://prove2.me/submissions/2f1d2e51-c8b5-4ed9-85f7-9fa72fcd8c74

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_AnalyticCharts_Osgood
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PRiemannExtensionSlices
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_norm_torusMap_sub
import Theorems.Thm_ReciprocityTheory_AnForm_Osgood_torusMap_mem_closedBall


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
theorem _root_.solution {n : ℕ} {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (θ : Fin n → ℝ) :
    torusMap (0 : Fin n → ℂ) (fun _ => r) θ ∈ ball (0 : Fin n → ℂ) 1 ∧
      ∀ i, torusMap (0 : Fin n → ℂ) (fun _ => r) θ i ≠ 0 := by
  refine ⟨closedBall_subset_ball hr1 (torusMap_mem_closedBall 0 hr0.le θ), fun i h => ?_⟩
  have h1 := norm_torusMap_sub (0 : Fin n → ℂ) hr0.le θ i
  rw [h, Pi.zero_apply, sub_zero, norm_zero] at h1
  exact hr0.ne h1
end GroundTheory.Heights₂.Heights.Regular.RiemannExtensionSlices
