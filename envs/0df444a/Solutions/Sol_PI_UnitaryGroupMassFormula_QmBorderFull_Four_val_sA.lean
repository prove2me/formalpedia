-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.val_sA
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:50.668239+00:00
-- url     : https://prove2.me/submissions/fdfad10e-671f-47a9-a908-d74086e5728e

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
theorem _root_.solution {n : ℕ} (p : Fin (n + 1)) (k : Fin n) :
    (p.succAbove k).val = if k.val < p.val then k.val else k.val + 1 := by
  by_cases h : k.val < p.val
  · rw [if_pos h, Fin.succAbove_of_castSucc_lt _ _ (by simpa [Fin.lt_def] using h)]
    rfl
  · rw [if_neg h, Fin.succAbove_of_le_castSucc _ _ (by simpa [Fin.le_def] using not_lt.mp h)]
    rfl
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
