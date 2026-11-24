-- Prove2me | solution 1 for PI.OddDualWeyl.EvA.det_revCol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:44.136582+00:00
-- url     : https://prove2.me/submissions/35352e2c-9d43-42a8-9a27-d813a028e739

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_EvalDuality
import Theorems.Thm_PI_OddDualWeyl_EvA_revCol_eq

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
open PI PI.OddDualWeyl PI.OddDualWeyl.EvA
open Red
variable {K : Type} [Field K]
namespace PI.OddDualWeyl.EvA
theorem _root_.solution {m : ℕ} (A : Matrix (Fin (m + 1)) (Fin (m + 1)) K) :
    (revCol A).det = A.det * sgnK K m := by
  rw [revCol_eq A, Matrix.det_mul]
  all_goals rfl
end PI.OddDualWeyl.EvA
