-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_SubFamilyTwistPow_proof_5c5dd07705d5
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T08:27:04.176031+00:00
-- url     : https://prove2.me/submissions/e6bd4adc-41cf-46f8-9821-5ec22cf70eb7

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_SubFamilyTwistPowSt
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PSubFamilyTwistPow
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_SubFamily_exists_pow_6e2f7e5f6f11

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
namespace SubFamilyTwistPow
theorem _root_.solution : SubFamilyTwistPow.Statement.{u, v, w} := by
  intro S _ Ω _ _ N x E _ _ _ _ F Q a
  obtain ⟨P, hP⟩ := SubFamily.exists_pow Q a
  exact ⟨F.twistFam P, by rw [← hP]; rfl⟩
end SubFamilyTwistPow
end GroundTheory.Heights₂.Heights.Kleiman
