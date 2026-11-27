-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_TheoremB_CBounds_hypotheses_inhabited_42befe8fa3f0
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-27T05:08:47.959215+00:00
-- url     : https://prove2.me/submissions/6b2ddbc5-e9be-4bc5-8857-a4b15ae0505b

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_MultinomialWeights_StatementsEnd
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_TheoremB_uSample_dominant_24ae9bea4d88

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
noncomputable section
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.TheoremB
open MvPolynomial Finset Filter Topology
variable (d : IndexData)
variable {d}
namespace GroundTheory.Heights₂.Heights.TheoremB
namespace CBounds
theorem _root_.solution : IsDominant d1 (uR d1 uSample) := uSample_dominant
end CBounds
end GroundTheory.Heights₂.Heights.TheoremB
