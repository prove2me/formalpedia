-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_line_chow_415cb9fc03c2
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T08:33:32.460519+00:00
-- url     : https://prove2.me/submissions/694e958c-0beb-4b6b-9181-b45164bb0d37

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isProjPrime_line_6c88d2fbf567


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
open LineChowForm
namespace GroundTheory.Heights₂.Heights
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) :=
  ⟨isProjPrime_line, isChowForm_line⟩
end GroundTheory.Heights₂.Heights
