-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ThetaFirstCoordSplit_proof_7656e0b3166b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:50:34.171266+00:00
-- url     : https://prove2.me/submissions/54ac01f9-c39f-4445-b42f-a51b2c2c2a7e

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_StatementsTheta
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_ThetaGauss
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_CoordFirst
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_HeightKernels_PThetaFirstCoordSplit
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KThetaFirstCoordSplit_term_le_3db75cf9db45
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_KTheta_summable_exp_qf_4231a987a485


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
open Matrix Real
namespace GroundTheory.Heights₂.Heights
namespace ThetaFirstCoordSplit
theorem _root_.solution : ThetaFirstCoordSplit.Statement := by
  intro g _ Y ρ a u₁ hY hρ hρY
  have hs1 : Summable fun k : Fin g → ℤ => exp (-π * qf Y (intVec k + a + u₁)) := by
    have := KTheta.summable_exp_qf Y hY π pi_pos (a + u₁)
    simpa only [add_assoc] using this
  have hs2 : Summable fun k : Fin g → ℤ => exp (-(π / 2) * qf Y (intVec k + (a + u₁))) :=
    KTheta.summable_exp_qf Y hY (π / 2) (by positivity) (a + u₁)
  rw [← tsum_mul_left]
  exact Summable.tsum_le_tsum
    (fun k => KThetaFirstCoordSplit.term_le Y ρ a u₁ hY hρ hρY k) hs1 (hs2.mul_left _)
end ThetaFirstCoordSplit
end GroundTheory.Heights₂.Heights
