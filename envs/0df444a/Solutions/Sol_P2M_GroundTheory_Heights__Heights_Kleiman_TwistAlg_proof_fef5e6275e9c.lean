-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_Kleiman_TwistAlg_proof_fef5e6275e9c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:52.479747+00:00
-- url     : https://prove2.me/submissions/217b5e18-ac85-4510-8eda-e577bdbe215d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_StatementsStepTwo
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_TwistAlg
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_KleimanAmpleness_PTwistAlg
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_twistMul_twist_twistMul_1f133ffda355
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_Kleiman_pow_twistMul_3585a8ef645c


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
namespace GroundTheory.Heights₂.Heights.Kleiman
namespace TwistAlg
theorem _root_.solution : TwistAlg.Statement.{u, w} := by
  intro S _ Ω _ _ N x M p q m m' b₁ b₂ h
  rw [pow_twistMul, pow_twistMul, pow_twistMul, twistMul_twist_twistMul]
  congr 1
  · ring
  · push_cast
    linear_combination (b₁ : ℤ) * h
end TwistAlg
end GroundTheory.Heights₂.Heights.Kleiman
