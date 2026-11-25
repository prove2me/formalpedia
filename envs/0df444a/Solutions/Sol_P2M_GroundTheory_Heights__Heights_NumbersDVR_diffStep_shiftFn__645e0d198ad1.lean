-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_shiftFn__645e0d198ad1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T04:41:47.965676+00:00
-- url     : https://prove2.me/submissions/12fb117a-2bbc-4d70-ba17-020863c183aa

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_StatementsCN
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_PMixedDiffLinear

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.NumbersDVR
variable {K : Type*}
namespace GroundTheory.Heights₂.Heights.NumbersDVR
theorem _root_.solution (b s : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (shiftFn s f) = shiftFn s (diffStep b f) := by
  funext m; simp only [diffStep, shiftFn, sub_right_comm]
end GroundTheory.Heights₂.Heights.NumbersDVR
