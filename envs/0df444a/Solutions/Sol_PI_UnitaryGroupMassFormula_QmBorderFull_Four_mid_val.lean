-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.mid_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T08:47:10.424994+00:00
-- url     : https://prove2.me/submissions/ad6b1da0-ec25-4639-ba80-8bf65b58fc9e

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
theorem _root_.solution {n t : ℕ} (e es : Fin n) (F : Fin t → Fin n) (j : Fin t) :
    bE e (bS F es) j.castSucc.succ = F j := by
  simp [bE, bS]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
