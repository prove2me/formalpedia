-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.rw_zero
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:42:02.358614+00:00
-- url     : https://prove2.me/submissions/5993f918-03d1-4f59-b1bf-1304514324a3

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
theorem _root_.solution {n k : ℕ} (e es : Fin n) (v : Fin (k + 1) → Fin n) (w : Fin (k + 1)) :
    (bE e (bS v es) ∘ (w.castSucc.succ).succAbove) 0 = e := by
  first
  | simp [bE]
  | (show bE e (bS v es) ((w.castSucc.succ).succAbove 0) = e; rw [Fin.succ_succAbove_zero]; simp only [bE, Fin.cons_zero])
end PI.UnitaryGroupMassFormula.QmBorderFull
