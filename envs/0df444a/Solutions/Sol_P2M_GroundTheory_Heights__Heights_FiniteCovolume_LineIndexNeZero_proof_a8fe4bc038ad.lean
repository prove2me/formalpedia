-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_FiniteCovolume_LineIndexNeZero_proof_a8fe4bc038ad
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T08:01:14.10927+00:00
-- url     : https://prove2.me/submissions/be91b8da-26a0-451a-b539-2026527d2494

import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Gub1_proof__5e3557ef2b02
import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PVectorOrbitsFinite
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ImportsTerExtra
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_FiniteCovolume_PLineIndexNeZero
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_CongruenceUnitsFiniteIndex_proof_eec00df32b44
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_FiniteCovolume_VectorOrbitsFinite_proof_a256cbf4870a


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.FiniteCovolume
open NumberField
namespace GroundTheory.Heights₂.Heights.FiniteCovolume
namespace LineIndexNeZero
theorem _root_.solution (E W : Type*) [Field E] [NumberField E] [AddCommGroup W]
    [Module E W] : LineIndexNeZero.Statement E W :=
  _root_.P2M_UpperTheory_Reformulated_B_Gub1_proof__5e3557ef2b02 E W
end LineIndexNeZero
end GroundTheory.Heights₂.Heights.FiniteCovolume
