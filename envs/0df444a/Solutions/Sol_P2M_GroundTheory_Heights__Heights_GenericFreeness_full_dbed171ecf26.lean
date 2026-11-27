-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_GenericFreeness_full_dbed171ecf26
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-27T04:55:06.03598+00:00
-- url     : https://prove2.me/submissions/2d70efec-d741-4d5f-bd05-8b3469ac2126

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreeness
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericNoetherNormalisation
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ComplexAnalyticSets_PGenericFreenessClosed
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericFreeness_proof_71d66b879eb6
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_GenericNoetherNormalisation_proof_35692972779d
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_GenericNoetherNormalisationCapelliIdentities_proof__e6cd435f9dea
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qn10_sum_r_mul_ne__f17edb41f5d8


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
universe u v w
namespace GroundTheory.Heights₂.Heights
namespace GenericFreeness
theorem _root_.solution : GenericFreeness.Statement.{u, v, w} :=
  GenericFreeness.proof GenericNoetherNormalisation.proof
end GenericFreeness
end GroundTheory.Heights₂.Heights
