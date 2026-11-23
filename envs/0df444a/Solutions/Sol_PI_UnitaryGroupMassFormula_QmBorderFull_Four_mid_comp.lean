-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.mid_comp
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:10.384423+00:00
-- url     : https://prove2.me/submissions/cb2935ee-bbd7-4b0b-968a-7974e97e6a18

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp

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
theorem _root_.solution {n t : ℕ} (e es : Fin n) (F : Fin (t + 1) → Fin n) (p : Fin (t + 1)) :
    bE e (bS F es) ∘ (p.castSucc.succ).succAbove = bE e (bS (F ∘ p.succAbove) es) := by
  funext i
  refine Fin.cases ?_ (fun i' => ?_) i
  · simp [bE]
  · simp only [Function.comp_apply, bE, Fin.succ_succAbove_succ, Fin.cons_succ]
    refine Fin.lastCases ?_ (fun i'' => ?_) i'
    · rw [Fin.succAbove_ne_last_last (Fin.castSucc_lt_last p).ne]
      simp [bS]
    · rw [Fin.castSucc_succAbove_castSucc]
      simp [bS]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
