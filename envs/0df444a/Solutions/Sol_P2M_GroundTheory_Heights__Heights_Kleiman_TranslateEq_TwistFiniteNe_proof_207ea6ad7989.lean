-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_TwistFiniteNe_proof_207ea6ad7989
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:55.765172+00:00
-- url     : https://prove2.me/submissions/5d3e2f20-49d0-4cf6-8cf9-4cd35ace401f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistPowZeroSub
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwinEqBundle
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PTwistFiniteNe
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_LineBundle_proof_28c071628e88
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TranslateEq_TwistFinite_equiv_ne_95f509a2a8e9


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Heights₂ GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.Kleiman GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
namespace TwistFiniteNe
theorem _root_.solution (hT1 : Kleiman.TwistFinite.Statement.{0, 0}) : TwistFiniteNe.Statement :=
  (TwistFinite.equiv_ne LineBundle.proof).mp hT1
end TwistFiniteNe
end GroundTheory.Heights₂.Heights.Kleiman.TranslateEq
