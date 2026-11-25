-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.sign_pair_succAbove_right
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:41:48.840175+00:00
-- url     : https://prove2.me/submissions/de8852ad-2363-46c1-a2d2-11fe58b26c3f

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
theorem _root_.solution {k : ℕ} (w : Fin (k + 1)) (j : Fin k) :
    sg2 w (w.succAbove j) = (-1 : ℤ) ^ ((w : ℕ) + (j : ℕ)) := by
  unfold sg2
  rcases lt_or_ge (j : ℕ) (w : ℕ) with h | h
  · have hv : (w.succAbove j).val = j := by rw [val_sA, if_pos h]
    rw [if_pos (by rw [hv]; exact h), hv]
  · have hv : (w.succAbove j).val = j + 1 := by rw [val_sA, if_neg (by omega)]
    rw [if_neg (by rw [hv]; omega), hv, show (w : ℕ) + (j + 1) + 1 = (w + j) + 2 by ring, pow_add]
    norm_num
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
