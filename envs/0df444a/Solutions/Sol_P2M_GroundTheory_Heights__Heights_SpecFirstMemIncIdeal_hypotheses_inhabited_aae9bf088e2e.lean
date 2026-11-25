-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_SpecFirstMemIncIdeal_hypotheses_inhabited_aae9bf088e2e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T10:01:17.037833+00:00
-- url     : https://prove2.me/submissions/8016b0cc-6600-4f41-970e-65c80a26042d

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_uLine_fb22ac47c882
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_LineChowForm_isChowForm_line_d0d771512121


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
namespace SpecFirstMemIncIdeal
theorem _root_.solution :
    IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ≤ Ideal.span {X 0} ∧
      linForm uLine ∈ Ideal.span {(X 0 : MvPolynomial (Fin 2) ℚ)} :=
  ⟨isChowForm_line, bot_le, by rw [linForm_uLine]; exact Ideal.mem_span_singleton_self _⟩
end SpecFirstMemIncIdeal
end GroundTheory.Heights₂.Heights
