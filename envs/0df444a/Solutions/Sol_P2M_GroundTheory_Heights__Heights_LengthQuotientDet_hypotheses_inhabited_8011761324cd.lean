-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_LengthQuotientDet_hypotheses_inhabited_8011761324cd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:32:09.101473+00:00
-- url     : https://prove2.me/submissions/2249b06a-bea5-4802-8ee6-7f53382fa27d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements

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
open MvPolynomial
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace LengthQuotientDet
theorem _root_.solution :
    LinearMap.det ((2 : ℤ_[2]) • LinearMap.id : ℤ_[2] →ₗ[ℤ_[2]] ℤ_[2]) ≠ 0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [LinearMap.det_smul, LinearMap.det_id, mul_one, Module.finrank_self, pow_one]
  exact two_ne_zero
end LengthQuotientDet
end GroundTheory.Heights₂.Heights
