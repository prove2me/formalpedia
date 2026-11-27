-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Model_DominatingDVRScheme_proof_f0939e34e365
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-27T05:02:51.759352+00:00
-- url     : https://prove2.me/submissions/a4c539d6-85f7-43f1-9ad0-298355bac4c0

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVR
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizuki
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PKrullAkizukiQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PTorsionFreeQuotientLength
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PBlowUpChart
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_IntegralModels_PDominatingDVRScheme
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_DominatingDVR_closed_974669d55d52
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Model_not_isField_stalk_of_ne_genericPoint_1cad4102bfa7

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Model
open AlgebraicGeometry
namespace GroundTheory.Heights₂.Heights.Model
namespace DominatingDVRScheme
theorem _root_.solution : DominatingDVRScheme.Statement := by
  intro Z _ _ z hz
  exact DominatingDVR.closed (Z.presheaf.stalk z) (not_isField_stalk_of_ne_genericPoint Z z hz)
    Z.functionField
end DominatingDVRScheme
end GroundTheory.Heights₂.Heights.Model
