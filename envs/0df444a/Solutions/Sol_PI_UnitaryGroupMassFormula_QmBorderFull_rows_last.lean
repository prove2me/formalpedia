-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.rows_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:53.891652+00:00
-- url     : https://prove2.me/submissions/91a7d12f-181a-4b1d-a14e-f140cfd87dd6

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
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ (Fin.last (k + 1)).succAbove = bE e (v ∘ w.succAbove) := by
  funext j
  have hw := w.isLt
  refine Fin.cases ?_ (fun j => ?_) j
  · simp only [Function.comp_apply]
    have h0 : (Fin.last (k + 1)).succAbove 0 = 0 := Fin.ext (by rw [val_succAbove]; simp)
    rw [h0, Fin.succ_succAbove_zero]
    simp only [bE, Fin.cons_zero]
  · simp only [Function.comp_apply]
    have hj := j.isLt
    have h1 : (w.castSucc.succ).succAbove ((Fin.last (k + 1)).succAbove j.succ) = (Fin.castSucc (w.succAbove j)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
    rw [h1]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_castSucc, Function.comp_apply]
end PI.UnitaryGroupMassFormula.QmBorderFull
