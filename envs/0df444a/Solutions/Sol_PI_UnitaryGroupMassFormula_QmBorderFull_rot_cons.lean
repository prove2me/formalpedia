-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.rot_cons
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:50.736148+00:00
-- url     : https://prove2.me/submissions/d09246d8-5211-412e-8378-340f4c6f32e3

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipOneEqSuccAbove

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
theorem _root_.solution {n k : ℕ} (e : Fin n) (W : Fin k → Fin n) :
    bE e W = Fin.snoc (α := fun _ => Fin n) W e ∘ (finRotate (k + 1)).symm := by
  first
  | (rw [Fin.snoc_eq_cons_rotate]; funext i; simp [bE])
  | (funext i; obtain ⟨j, rfl⟩ := (finRotate (k + 1)).surjective i; simp only [Function.comp_apply, Equiv.symm_apply_apply, bE]; induction j using Fin.lastCases <;> simp [finRotate_last, finRotate_succ_apply])
end PI.UnitaryGroupMassFormula.QmBorderFull
