-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.sign_two_succAbove_left
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:41:50.53713+00:00
-- url     : https://prove2.me/submissions/de9fcc52-48e8-47e0-814d-aac48a7d100c

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
theorem _root_.solution {k : ℕ} (x : Fin (k + 1)) (y : Fin k) :
    sg2 (x.succAbove y) x = -(-1 : ℤ) ^ ((x : ℕ) + (y : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (y : ℕ) (x : ℕ) with h | h
  · have hv : (x.succAbove y).val = y := by rw [val_sA, if_pos h]
    rw [if_neg (by rw [hv]; omega), hv, pow_succ, add_comm (y : ℕ)]
    ring
  · have hv : (x.succAbove y).val = y + 1 := by rw [val_sA, if_neg (by omega)]
    rw [if_pos (by rw [hv]; omega), hv, show (y : ℕ) + 1 + x = (x + y) + 1 by ring, pow_succ]
    ring
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
