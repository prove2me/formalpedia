-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_IncIdealDim_hypotheses_inhabited_7986e28bcc3e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:54:59.283703+00:00
-- url     : https://prove2.me/submissions/af5d1d49-9df2-42eb-9b2f-a6f74f7ef624

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Imports
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_ringKrullDim_quot_bot_acd27392687d


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
namespace IncIdealDim
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) =
        ((0 + 1 : ℕ) : WithBot ℕ∞) :=
  ⟨isProjPrime_point ℚ, ringKrullDim_quot_bot ℚ 1⟩
end IncIdealDim
end GroundTheory.Heights₂.Heights
