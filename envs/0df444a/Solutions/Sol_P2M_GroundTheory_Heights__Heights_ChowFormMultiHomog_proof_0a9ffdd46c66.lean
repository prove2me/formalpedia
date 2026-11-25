-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormMultiHomog_proof_0a9ffdd46c66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:37:06.073038+00:00
-- url     : https://prove2.me/submissions/1455ca12-24b8-4d9a-8528-6387439f0b9f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ChowFormHomog
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_PChowFormMultiHomog
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_chowFormMultiHomog_58d4a94209bb

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
namespace ChowFormMultiHomog
theorem _root_.solution (_h₁ : ProjNullstellensatz.Statement) :
    ChowFormMultiHomog.Statement :=
  chowFormMultiHomog
end ChowFormMultiHomog
end GroundTheory.Heights₂.Heights
