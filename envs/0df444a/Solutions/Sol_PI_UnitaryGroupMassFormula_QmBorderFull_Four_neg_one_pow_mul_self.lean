-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.neg_one_pow_mul_self
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:17:46.977234+00:00
-- url     : https://prove2.me/submissions/925cacbe-7ac9-4dda-a38a-b98b29d26dd1

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
theorem _root_.solution (t : ℕ) : ((-1 : ℤ) ^ t) * ((-1 : ℤ) ^ t) = 1 := by
  rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
