-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.rows_succ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:57:44.915732+00:00
-- url     : https://prove2.me/submissions/f59fd68d-7b7c-4e75-9a47-b4eaebd197ff

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_val_succAbove
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_skip_one_eq_succAbove

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
theorem _root_.solution {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1))
    (h : k + 1 = k + 1 - 1 + 1) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) ∘ Fin.succ =
      Fin.snoc (α := fun _ => Fin n) (v ∘ skip1 w) es ∘ Fin.cast h := by
  funext j
  simp only [Function.comp_apply]
  have hw := w.isLt
  refine Fin.lastCases ?_ (fun j => ?_) j
  · have h1 : (w.castSucc.succ).succAbove (Fin.last k).succ = (Fin.last (k + 1)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc, Fin.val_last]; split_ifs <;> omega)
    rw [h1]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_last, Fin.cast_last]
  · have hj := j.isLt
    have h2 : (w.castSucc.succ).succAbove (Fin.castSucc j).succ = (Fin.castSucc (w.succAbove j)).succ :=
      Fin.ext (by simp only [val_succAbove, Fin.val_succ, Fin.coe_castSucc]; split_ifs <;> omega)
    have h3 : Fin.cast h (Fin.castSucc j) = Fin.castSucc (Fin.cast (by omega) j : Fin (k + 1 - 1)) :=
      Fin.ext (by simp only [Fin.coe_cast, Fin.coe_castSucc])
    rw [h2, h3]
    simp only [bE, bS, Fin.cons_succ, Fin.snoc_castSucc, Function.comp_apply]
    rw [skip_one_eq_succAbove]
    rfl
end PI.UnitaryGroupMassFormula.QmBorderFull
