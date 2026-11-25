-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChowDegreePos_hypotheses_inhabited_7362a1aae6a4
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:47.159367+00:00
-- url     : https://prove2.me/submissions/8719a6c9-b204-4219-a65e-0e554b00c773

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_MahlerSectionBasic
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_ContinuousHermNormGroup
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_StatementsMahler
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isChowForm_point_62847896aaea
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isMultiHomog_point_50a43e297f77
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
open MvPolynomial MeasureTheory Matrix
noncomputable section
variable {n : ℕ}
namespace GroundTheory.Heights₂.Heights
namespace ChowDegreePos
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) ∧ IsChowForm (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)) 1 (X (0, 0)) ∧
      IsMultiHomog 1 (X (0, 0) : MvPolynomial (Fin 1 × Fin 1) ℂ) :=
  ⟨isProjPrime_point ℂ, isChowForm_point ℂ, isMultiHomog_point ℂ⟩
end ChowDegreePos
end GroundTheory.Heights₂.Heights
