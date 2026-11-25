-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.rw_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:59.29988+00:00
-- url     : https://prove2.me/submissions/3c8b7b4c-6ab0-49cc-9043-df0e47d5849f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_val_succAbove

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
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.QmBorderFull
open PI
namespace PI.UnitaryGroupMassFormula.QmBorderFull
theorem _root_.solution {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) (Fin.last (k + 1)) = es := by
  show bE e (bS v es) ((w.castSucc.succ).succAbove (Fin.last (k + 1))) = es
  have hw := w.isLt
  have h1 : (w.castSucc.succ).succAbove (Fin.last (k + 1)) = (Fin.last (k + 1)).succ :=
    Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
  rw [h1]
  simp only [bE, bS, Fin.cons_succ, Fin.snoc_last]
end PI.UnitaryGroupMassFormula.QmBorderFull
