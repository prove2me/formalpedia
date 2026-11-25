-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_ChartNorm_hypotheses_inhabited_d6dbdf78dc79
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:49.694338+00:00
-- url     : https://prove2.me/submissions/c8451e93-21e3-4fa8-95c4-87587c87134f

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_prime_qLine_c53c4192a86d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_span_qLine_075a81a8981f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_specFirst_tLine_not_mem_ccadebe4d4f7
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
namespace ChartNorm
theorem _root_.solution :
    IsProjPrime (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      (Ideal.span {qLine}).IsPrime ∧
      (Ideal.span {qLine} = ⊥ ∨ ∃ q, Prime q ∧ Ideal.span {qLine} = Ideal.span {q}) ∧
      specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine ∉ Ideal.span {qLine} :=
  ⟨isProjPrime_line, isChowForm_line, isPrime_span_qLine, Or.inr ⟨qLine, prime_qLine, rfl⟩,
    specFirst_tLine_not_mem⟩
end ChartNorm
end GroundTheory.Heights₂.Heights
