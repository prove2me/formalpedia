-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.QmBorderFull.Four.scal
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:37:00.033338+00:00
-- url     : https://prove2.me/submissions/a6234294-a834-4519-92cc-57a33b535278

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_BorderMinorRotation_SkipTwoSuccAboveComp
import Theorems.Thm_PI_UnitaryGroupMassFormula_QmBorderFull_Four_neg_one_pow_mul_self

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
theorem _root_.solution (k w j x y : ℕ) :
    (-1 : ℤ) ^ (k + 1 + 1 + (j + 1)) * (-1 : ℤ) ^ (x + k + y) =
      (-1 : ℤ) ^ w * ((-1 : ℤ) ^ (w + j) * -(-1 : ℤ) ^ (x + y)) := by
  have hk := neg_one_pow_mul_self k
  have hw := neg_one_pow_mul_self w
  linear_combination (-(-1 : ℤ) ^ (j + x + y)) * hk + ((-1 : ℤ) ^ (j + x + y)) * hw
end PI.UnitaryGroupMassFormula.QmBorderFull.Four
