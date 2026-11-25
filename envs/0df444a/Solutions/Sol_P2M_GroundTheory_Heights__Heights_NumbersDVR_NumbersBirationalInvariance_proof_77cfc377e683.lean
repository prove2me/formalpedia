-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_NumbersDVR_NumbersBirationalInvariance_proof_77cfc377e683
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T13:09:43.172279+00:00
-- url     : https://prove2.me/submissions/afa2fcce-0df5-47b0-9ef7-0eb4af890ea5

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_Length
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_MemOfMemSupportDivCycle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_DiscreteValuationNumbers_OrdModEqLengthQuotSup
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_NumbersBirationalInvariance_of_lengthFormulaDimOne_85e85bedf190
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_NumbersDVR_lengthFormulaDimOne_ebd95ca81df3


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
open Module IsLocalRing ReciprocityTheory.ChartRestriction.G.AI
universe u v
namespace GroundTheory.Heights₂.Heights.NumbersDVR
namespace NumbersBirationalInvariance
theorem _root_.solution : IndefiniteRowSideFullHecke.NumbersDVR.NumbersBirationalInvariance.Statement.{u, v} :=
  NumbersBirationalInvariance.of_lengthFormulaDimOne lengthFormulaDimOne
end NumbersBirationalInvariance
end GroundTheory.Heights₂.Heights.NumbersDVR
