-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_AffineChartTrdeg_hypotheses_inhabited_a932ccbce1d8
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-27T04:52:30.428315+00:00
-- url     : https://prove2.me/submissions/66638c70-7c33-4079-adf5-d1346da5fd83

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_ImportsAlt
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
namespace AffineChartTrdeg
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      ringKrullDim (MvPolynomial (Fin 1) ℚ ⧸ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ))) =
        ((0 + 1 : ℕ) : WithBot ℕ∞) ∧
      (X 0 : MvPolynomial (Fin 1) ℚ) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨isProjPrime_point ℚ, ringKrullDim_quot_bot ℚ 1, by rw [Ideal.mem_bot]; exact X_ne_zero 0⟩
end AffineChartTrdeg
end GroundTheory.Heights₂.Heights
