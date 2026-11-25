-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowHeightRecursion_hypotheses_inhabited_a59b12a05d49
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T08:55:20.908109+00:00
-- url     : https://prove2.me/submissions/8332244c-d7a0-42e5-a055-08325b7ab3c2

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_Statements
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isProjPrime_point_e4b734f59300
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_point_50a43e297f77
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
namespace ChowHeightRecursion
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) (0 + 1) (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin (0 + 1) × Fin 1) ℚ) ∧
      linForm (fun j => (((fun _ => (1 : 𝓞 ℚ)) : Fin 1 → 𝓞 ℚ) j : ℚ)) ∉
        (⊥ : Ideal (MvPolynomial (Fin 1) ℚ)) := by
  refine ⟨isProjPrime_point ℚ, isChowForm_point ℚ, isMultiHomog_point ℚ, ?_⟩
  simpa using linForm_one_not_mem_point ℚ
end ChowHeightRecursion
end GroundTheory.Heights₂.Heights
