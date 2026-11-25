-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_exists_lipschitz_near_compact_eeaef94d801a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:32:14.311738+00:00
-- url     : https://prove2.me/submissions/85ab88a0-2ae3-4c7d-acb6-2ae08bcf0a66

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_BoundedStatements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_IsCompactImageClosureMid
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_GlueCharts
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PChartComparison
import Definitions.Def_ReciprocityTheory_AnalyticForms_PlurisubharmonicFunctions_PshMoll
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PBoundedChartComparison
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_le__638c0d78514a
import Theorems.Thm_P2M_ReciprocityTheory_AnForm_A_polyMax_mono__555a93f5b347
import Theorems.Thm_ReciprocityTheory_AnForm_A_le_polyMax
import Theorems.Thm_ReciprocityTheory_AnForm_A_mollify_thm


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
open Metric Set
open ReciprocityTheory.AnForm.A (IsPsh polyMax molli mollify_thm polyMax_le' polyMax_mono' le_polyMax)
open ReciprocityTheory.AnForm.M (FinHolAtlas)
noncomputable section
namespace GroundTheory.Heights₂.Heights.Regular
theorem _root_.solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F] {f : E → F} {K W : Set E}
    (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) (hf : ∀ y ∈ W, ContDiffAt ℝ 1 f y) :
    ∃ δ > 0, ∃ L : ℝ, ∀ z ∈ K, ∀ y ∈ closedBall z δ, y ∈ W ∧ ‖f y - f z‖ ≤ L * ‖y - z‖ := by
  obtain ⟨δ, hδ, hsub⟩ := hK.exists_cthickening_subset_open hW hKW
  have hcont : ContinuousOn (fderiv ℝ f) W :=
    ContDiffOn.continuousOn_fderiv_of_isOpen (fun y hy => (hf y hy).contDiffWithinAt) hW le_rfl
  obtain ⟨L, hL⟩ := (hK.cthickening (r := δ)).exists_bound_of_continuousOn (hcont.mono hsub)
  refine ⟨δ, hδ, L, fun z hz y hy => ⟨hsub (closedBall_subset_cthickening hz δ hy), ?_⟩⟩
  have hB : closedBall z δ ⊆ W := (closedBall_subset_cthickening hz δ).trans hsub
  exact (convex_closedBall z δ).norm_image_sub_le_of_norm_fderiv_le
    (fun w hw => (hf w (hB hw)).differentiableAt one_ne_zero)
    (fun w hw => hL w (closedBall_subset_cthickening hz δ hw)) (mem_closedBall_self hδ.le) hy
end GroundTheory.Heights₂.Heights.Regular
