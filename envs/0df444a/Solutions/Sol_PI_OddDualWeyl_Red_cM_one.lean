-- Prove2me | solution 1 for PI.OddDualWeyl.Red.cM_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:25.720621+00:00
-- url     : https://prove2.me/submissions/00d5ac4f-e895-4194-8761-dac81ddf01bf

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial Matrix
noncomputable section
open PI PI.OddDualWeyl PI.OddDualWeyl.Red
variable {R : Type*} [CommRing R] {k : ℕ}
namespace PI.OddDualWeyl.Red
theorem _root_.solution : cM (1 : Matrix (Fin k) (Fin k) R) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [cM, Matrix.one_apply, h]
end PI.OddDualWeyl.Red
