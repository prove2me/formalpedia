-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_comm__50e9b5a46128
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:12:35.624774+00:00
-- url     : https://prove2.me/submissions/0faac190-98d6-451e-9ed1-7c3a153fd025

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
theorem _root_.solution (b b' : K → ℤ) (f : (K → ℤ) → ℤ) :
    diffStep b (diffStep b' f) = diffStep b' (diffStep b f) := by
  funext m; simp only [diffStep, sub_right_comm m b b']; ring
end GroundTheory.Heights₂.Heights.NumbersDVR
