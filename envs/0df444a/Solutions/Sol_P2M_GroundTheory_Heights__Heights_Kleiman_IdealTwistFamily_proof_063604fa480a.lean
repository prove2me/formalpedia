-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_proof_063604fa480a
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:42:49.872541+00:00
-- url     : https://prove2.me/submissions/c8dc06b5-4972-4c41-b29f-3c6b268ade76

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsIdealTwist
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PIdealTwistFamily
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_sub_eq_mul_97ce44c60ed2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_idealMod_fg_96ac575d611f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_IdealTwistFamily_twist_mem_iff_e4733d843f95

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
universe u w
open GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
namespace GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
theorem _root_.solution : IdealTwistFamily.Statement := by
  intro S _ _ Ω _ _ N x Q J' hJ'
  refine ⟨{ Q.twist (idealSys x J') with mem_iff := twist_mem_iff Q J' }, rfl, fun I => ?_⟩
  change ((Q.twist (idealSys x J')).sub I).FG
  rw [twist_sub_eq_mul]
  exact (idealMod_fg J' hJ' I).mul (Q.fg I)
end GroundTheory.Heights₂.Heights.Kleiman.IdealTwistFamily
