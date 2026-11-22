-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.Tm_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:01:43.567645+00:00
-- url     : https://prove2.me/submissions/b5dab6dc-83f1-4b8b-b7b6-ea5a013f9060

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
theorem _root_.solution {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) {a b : Fin n}
    (h : a ≠ b) : Tm E u a b = E a b := by
  unfold Tm
  simp [h]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
