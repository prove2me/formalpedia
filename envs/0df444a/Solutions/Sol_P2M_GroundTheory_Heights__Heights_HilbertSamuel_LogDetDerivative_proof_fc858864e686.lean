-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_proof_fc858864e686
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-27T04:57:39.893447+00:00
-- url     : https://prove2.me/submissions/65194580-8aaf-4cf0-946f-fd4ca454cd01

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_StatementsLattice
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_HasDerivAtDet
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HilbertSamuel_PLogDetDerivative
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_HilbertSamuel_LogDetDerivative_intersectionNumber_baseChange_380f38d27535


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.HilbertSamuel
namespace GroundTheory.Heights₂.Heights.HilbertSamuel
namespace LogDetDerivative
theorem _root_.solution : LogDetDerivative.Statement :=
  LogDetDerivative.intersectionNumber_baseChange
end LogDetDerivative
end GroundTheory.Heights₂.Heights.HilbertSamuel
