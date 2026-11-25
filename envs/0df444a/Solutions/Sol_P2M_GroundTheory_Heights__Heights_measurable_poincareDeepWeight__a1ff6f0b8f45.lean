-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_measurable_poincareDeepWeight__a1ff6f0b8f45
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:38:41.217503+00:00
-- url     : https://prove2.me/submissions/c738602f-7f7c-4d08-a275-589b2bb01986

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_StTubeDeepWeightMass
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PTubeDeepWeightMass

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
open MeasureTheory Filter Topology
noncomputable section
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : Measurable poincareDeepWeight := by
  have hn : Measurable fun z : ℂ => ‖z‖ ^ 2 := (continuous_norm.pow 2).measurable
  exact Measurable.ite (measurableSet_lt hn.log measurable_const) (hn.mul (hn.log.pow_const 2)).inv
    measurable_const
end GroundTheory.Heights₂.Heights
