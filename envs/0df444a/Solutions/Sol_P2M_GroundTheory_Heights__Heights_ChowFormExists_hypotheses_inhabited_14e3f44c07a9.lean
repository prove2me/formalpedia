-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormExists_hypotheses_inhabited_14e3f44c07a9
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:33:55.326823+00:00
-- url     : https://prove2.me/submissions/76494d77-2591-4c60-b3ed-8173286212af

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quot_bot_acd27392687d
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
namespace ChowFormExists
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) =
        ((1 : ℕ) : WithBot ℕ∞) :=
  ⟨isProjPrime_point ℚ, ringKrullDim_quot_bot ℚ 1⟩
end ChowFormExists
end GroundTheory.Heights₂.Heights
