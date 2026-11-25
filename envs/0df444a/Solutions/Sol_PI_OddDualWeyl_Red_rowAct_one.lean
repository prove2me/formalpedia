-- Prove2me | solution 1 for PI.OddDualWeyl.Red.rowAct_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T10:18:36.702915+00:00
-- url     : https://prove2.me/submissions/04a2af69-e6e5-43f4-8dfb-60186322315d

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_sbs_genM
import Theorems.Thm_PI_OddDualWeyl_Red_cM_one
import Theorems.Thm_PI_OddDualWeyl_Red_rowAct_eq

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
theorem _root_.solution (p : MvPolynomial (Fin k × Fin k) R) : rowAct R (1 : Matrix (Fin k) (Fin k) R) p = p := by
  rw [rowAct_eq, cM_one, Matrix.one_mul, sbs_genM]
end PI.OddDualWeyl.Red
