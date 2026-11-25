-- Prove2me | solution 1 for P2M_GroundTheory_Heights__Heights_line_section_c9dd8470847c
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T08:55:30.689606+00:00
-- url     : https://prove2.me/submissions/2625d02f-12f5-4fdd-bd5b-b7bdadcc5ff9

import Mathlib
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_Statements
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ArithmeticBezout_LineInhabitant
import Definitions.Def_GroundTheory_HeightsAndTheta_Heights_ChowForms_StatementsSectionOrder
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_prime_qLine_c53c4192a86d
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_isPrime_span_qLine_075a81a8981f
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_not_dvd_specFirst_tLine_f8a08b7c59b2
import Theorems.Thm_P2M_GroundTheory_Heights__Heights_linForm_uLine_not_mem_bot_330a39a70e2d
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
      IsChowForm (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) (1 + 1) (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) ∧
      linForm uLine ∉ (⊥ : Ideal (MvPolynomial (Fin 2) ℚ)) ∧ Prime qLine ∧
      (Ideal.span {qLine}).IsPrime ∧
      ¬ qLine ∣ specFirst (D2 : MvPolynomial (Fin (1 + 1) × Fin 2) ℚ) tLine :=
  ⟨isProjPrime_line, isChowForm_line, linForm_uLine_not_mem_bot, prime_qLine, isPrime_span_qLine,
    not_dvd_specFirst_tLine⟩
end GroundTheory.Heights₂.Heights
