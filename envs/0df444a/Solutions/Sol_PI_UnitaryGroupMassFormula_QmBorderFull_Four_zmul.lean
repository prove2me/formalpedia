-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.zmul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:41:20.862874+00:00
-- url     : https://prove2.me/submissions/fa5e1b04-86ae-43dc-9e77-04652e4da59d

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
theorem _root_.solution {A : Type} [Ring A] (z : ℤ) (y : A) : (z : A) * y = z • y := by
  rw [zsmul_eq_mul]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
