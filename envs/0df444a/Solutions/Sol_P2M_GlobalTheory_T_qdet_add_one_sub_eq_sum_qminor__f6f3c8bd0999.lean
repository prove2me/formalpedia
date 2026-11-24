-- Prove2me | solution 1 for P2M_GlobalTheory_T_qdet_add_one_sub_eq_sum_qminor__f6f3c8bd0999
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T23:37:48.558254+00:00
-- url     : https://prove2.me/submissions/4107b5ba-df3c-477f-860d-5bee279581c7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetAddOneSubEqSumQminor
import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_QdetAddOneSubEqSumQminorStatement
import Theorems.Thm_GlobalTheory_qdet_add_one_sub_eq_sum_qminor


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Finset
set_option maxHeartbeats 1000000
namespace _root_.GlobalTheory.T
theorem _root_.solution : ∀ (A : Type) [Ring A] [Algebra ℂ A] (m : ℕ) (E : Fin (m + 1) → Fin (m + 1) → A) (u : ℂ), qdet E (u + 1) - qdet E u = ∑ i : Fin (m + 1), qminor E (Fin.succAbove i) (Fin.succAbove i) u := by
  first | exact @GlobalTheory.qdet_add_one_sub_eq_sum_qminor | exact GlobalTheory.qdet_add_one_sub_eq_sum_qminor | (intros; apply GlobalTheory.qdet_add_one_sub_eq_sum_qminor <;> assumption)
end _root_.GlobalTheory.T
