-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubFamilyTwist_proof_91489bdfeda3
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T05:02:26.864054+00:00
-- url     : https://prove2.me/submissions/d07d2ce2-5590-46fc-adf8-e77177f70b6d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubFamilyTwistPow
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ElementarySymmetric_PSubFamilyTwistX
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubSystem_twist_sub_fg_e9dce289dfcc

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
noncomputable section
universe u v w
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace SubFamilyTwist
theorem _root_.solution : SubFamilyTwist.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q hF
  exact ⟨F.twistFam Q.toSubFamily, rfl, fun I =>
    SubSystem.twist_sub_fg F.toSubSystem Q.toSubSystem I (hF I) (Q.fg I)⟩
end SubFamilyTwist
end GroundTheory.Heights₂.Heights.Kleiman
