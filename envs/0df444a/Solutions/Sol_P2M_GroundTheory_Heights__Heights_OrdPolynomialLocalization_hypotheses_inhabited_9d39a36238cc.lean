-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_OrdPolynomialLocalization_hypotheses_inhabited_9d39a36238cc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T09:33:53.451387+00:00
-- url     : https://prove2.me/submissions/8296dd78-de99-4099-a6bb-077487dc0199

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
namespace OrdPolynomialLocalization
theorem _root_.solution :
    (⊥ : Ideal ℤ).IsPrime ∧ (Ideal.map (C : ℤ →+* MvPolynomial Unit ℤ) ⊥).IsPrime := by
  rw [Ideal.map_bot]
  exact ⟨Ideal.isPrime_bot, Ideal.isPrime_bot⟩
end OrdPolynomialLocalization
end GroundTheory.Heights₂.Heights
