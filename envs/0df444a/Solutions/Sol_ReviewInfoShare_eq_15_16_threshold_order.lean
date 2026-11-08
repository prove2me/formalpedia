-- Prove2me | solution 1 for ReviewInfoShare.eq_15_16_threshold_order
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:15:05.013221+00:00
-- url     : https://prove2.me/submissions/5c4d1489-77f7-4f8e-bd0f-ac5fab0df3c5

import Mathlib
import Definitions.Def_ReviewInfoShare_Model
import Definitions.Def_ReviewInfoShare_Thresholds

open ReviewInfoShare in
theorem solution (P : Params) (hP : P.Admissible) :
    P.psiI0 < P.psiIInf ∧
    (P.pi .high < P.pi .low →
      (P.psiIInf < P.qH ^ 2 - P.qL ^ 2 ∨ P.qH ^ 2 - P.qL ^ 2 < P.psiI0) → P.phiI0 < P.phiIInf) := by
  have hσp : 0 < P.σp ^ 2 := pow_pos hP.σp_pos 2
  have hσθ : 0 < P.σθ ^ 2 := pow_pos hP.σθ_pos 2
  refine ⟨?_, fun hπ hcase => ?_⟩
  · unfold Params.psiI0 Params.psiIInf
    linarith
  · have hN : 0 < 2 * (P.pi .low - P.pi .high) := by linarith
    unfold Params.phiI0 Params.phiIInf
    unfold Params.psiI0 Params.psiIInf at hcase
    rcases hcase with h | h
    · have hB : 0 < P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2 - 1 / 3 * P.σp ^ 2) :=
        mul_pos hσθ (by linarith)
      have hBA : P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2 - 1 / 3 * P.σp ^ 2) <
          P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2) := mul_lt_mul_of_pos_left (by linarith) hσθ
      exact div_lt_div_of_pos_left hN hB hBA
    · have hA : 0 < -(P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2)) := by
        have : P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2) < 0 :=
          mul_neg_of_pos_of_neg hσθ (by linarith)
        linarith
      have hAB : -(P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2)) <
          -(P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2 - 1 / 3 * P.σp ^ 2)) := by
        have : P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2 - 1 / 3 * P.σp ^ 2) <
          P.σθ ^ 2 * (P.qH ^ 2 - 4 / 3 * P.qL ^ 2) := mul_lt_mul_of_pos_left (by linarith) hσθ
        linarith
      have := div_lt_div_of_pos_left hN hA hAB
      rw [div_neg, div_neg] at this
      linarith
