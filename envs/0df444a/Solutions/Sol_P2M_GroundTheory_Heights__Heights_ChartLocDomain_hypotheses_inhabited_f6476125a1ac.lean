-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartLocDomain_hypotheses_inhabited_f6476125a1ac
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:05:37.079323+00:00
-- url     : https://prove2.me/submissions/e31c4a05-7cb1-4106-846a-0d79fcd2ac1a

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_span_qLine_075a81a8981f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_tLine_not_mem_bot_4c07bc61bfd4
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
namespace ChartLocDomain
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      (Ideal.span {qLine}).IsPrime ∧ linForm tLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) :=
  ⟨isProjPrime_line, isChowForm_line, isPrime_span_qLine, linForm_tLine_not_mem_bot⟩
end ChartLocDomain
end GroundTheory.Heights₂.Heights
