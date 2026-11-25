-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormSection_hypotheses_inhabited_b7e6b352f62b
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:54:13.75616+00:00
-- url     : https://prove2.me/submissions/e1145c21-c0e3-4937-adf6-61890a9b02b9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_one_not_mem_point_805b757dbb4c

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
open MvPolynomial MeasureTheory NumberField
noncomputable section
namespace GroundTheory.Heights₂.Heights
namespace ChowFormSection
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun _ => (1 : ℚ)) ∉ (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) :=
  ⟨isProjPrime_point ℚ, isChowForm_point ℚ, linForm_one_not_mem_point ℚ⟩
end ChowFormSection
end GroundTheory.Heights₂.Heights
