-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.skip_two_succAbove_comp_alt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:43:25.787203+00:00
-- url     : https://prove2.me/submissions/54679dee-9e9d-4932-8b1c-74037b94c2ae

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_val_sA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL
noncomputable section
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull PI.UnitaryGroupMassFormula.QmBorderFull.Four
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull.Four
theorem _root_.solution {k : ℕ} (w : Fin (k + 2)) (j : Fin (k + 1)) (i : Fin k) :
    skip2 (min w (w.succAbove j)) (max w (w.succAbove j)) i = w.succAbove (j.succAbove i) := by
  apply Fin.ext
  have hv := val_sA w j
  rw [val_sA w (j.succAbove i), val_sA j i]
  unfold skip2
  rcases lt_or_ge (j : ℕ) (w : ℕ) with h | h
  · have hlt : w.succAbove j < w := by rw [Fin.lt_def, hv, if_pos h]; exact h
    rw [min_eq_right hlt.le, max_eq_left hlt.le]
    rw [if_pos h] at hv
    split_ifs <;> (simp_all; try omega)
  · have hle : w ≤ w.succAbove j := by rw [Fin.le_def, hv, if_neg (by omega)]; omega
    rw [min_eq_left hle, max_eq_right hle]
    rw [if_neg (by omega)] at hv
    split_ifs <;> (simp_all; try omega)
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
