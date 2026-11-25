-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_chowFormMultiHomog_58d4a94209bb
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T09:33:57.839416+00:00
-- url     : https://prove2.me/submissions/e500ddb4-c4c8-48d6-b46e-3de6497ef043

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog

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
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution : ChowFormMultiHomog.Statement :=
  fun _ _ _ _ _ _ hP hf => hf.exists_multiHomog hP
end GroundTheory.Heights₂.Heights
