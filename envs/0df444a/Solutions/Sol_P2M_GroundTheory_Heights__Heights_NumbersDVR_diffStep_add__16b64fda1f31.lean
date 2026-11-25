-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_diffStep_add__16b64fda1f31
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T04:41:47.970684+00:00
-- url     : https://prove2.me/submissions/c953a43d-9164-4724-a4d5-e303f5794400

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
theorem _root_.solution (b : K → ℤ) (f g : (K → ℤ) → ℤ) :
    diffStep b (f + g) = diffStep b f + diffStep b g := by
  funext m; simp only [diffStep, Pi.add_apply]; ring
end GroundTheory.Heights₂.Heights.NumbersDVR
