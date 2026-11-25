-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_LineTwist_proof_e6c76b662e59
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T06:37:37.832221+00:00
-- url     : https://prove2.me/submissions/7ba0b11c-1a0c-4d37-b050-0761026d8c5d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PLineTwist

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman
universe u w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace LineTwist
theorem _root_.solution : LineTwist.Statement.{u, w} :=
  fun _ _ _ _ _ _ _ Q₁ Q₂ => ⟨Q₁.tensorProd Q₂, rfl⟩
end LineTwist
end GroundTheory.Heights₂.Heights.Kleiman
