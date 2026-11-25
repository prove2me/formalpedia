-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowFormSectionVertical_hypotheses_inhabited_25f0794614ab
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T08:54:10.867886+00:00
-- url     : https://prove2.me/submissions/fc05ba8a-8338-455b-a2b1-4c35f9918e35

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
namespace ChowFormSectionVertical
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by
  refine ⟨isProjPrime_point ℚ, isChowForm_point ℚ, ?_⟩
  simpa using linForm_one_not_mem_point ℚ
end ChowFormSectionVertical
end GroundTheory.Heights₂.Heights
