-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Regular_ExpQuad_analyticAt_finsetSum_2318fa4c3e17
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:48:58.762787+00:00
-- url     : https://prove2.me/submissions/b7a68dbf-c3dd-42f6-a9c3-004e7e899a2d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StRiemannSlices
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StPuncturedExpOrder
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_StLogCoverDescent
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_Regularisation_PExpExtension

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
open Metric Filter Topology Matrix
noncomputable section
open GroundTheory.Heights₂.Heights.Regular.ExpQuad
namespace GroundTheory.Heights₂.Heights.Regular.ExpQuad
theorem _root_.solution {n : ℕ} {ι : Type*} (s : Finset ι) {f : ι → (Fin n → ℂ) → ℂ}
    {w : Fin n → ℂ} (h : ∀ i ∈ s, AnalyticAt ℂ (f i) w) :
    AnalyticAt ℂ (fun x => ∑ i ∈ s, f i x) w := by
  have := Finset.analyticAt_sum s h
  convert this using 1
  funext x
  simp [Finset.sum_apply]
end GroundTheory.Heights₂.Heights.Regular.ExpQuad
