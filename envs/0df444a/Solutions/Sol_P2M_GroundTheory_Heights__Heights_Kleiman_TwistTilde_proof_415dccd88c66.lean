-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistTilde_proof_415dccd88c66
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:03:01.999806+00:00
-- url     : https://prove2.me/submissions/63a019ea-2f56-4798-85b8-11ef83d2bd82

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistTildeSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistTilde
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_TwistTildeProof_twist_eq_8a835032af81

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
open MvPolynomial
noncomputable section
universe u v w
open TwistTildeProof
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TwistTilde
theorem _root_.solution : TwistTilde.Statement := by
  intro S _ Ω _ _ N x E _ _ _ _ M Q
  exact ⟨prod M Q, fun c => rfl, twist_eq M Q⟩
end TwistTilde
end GroundTheory.Heights₂.Heights.Kleiman
