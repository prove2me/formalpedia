-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncIdealPrime_hypotheses_inhabited_84cd1223ff65
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:33:36.499806+00:00
-- url     : https://prove2.me/submissions/d977e815-2afe-4530-bcc5-5237180b8463

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300


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
namespace IncIdealPrime
theorem _root_.solution :
    (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)).IsPrime ∧ IsRelevant (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨Ideal.isPrime_bot, (isProjPrime_point ℚ).isRelevant⟩
end IncIdealPrime
end GroundTheory.Heights₂.Heights
