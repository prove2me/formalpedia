-- Prove2me | solution 1 for PI.OddDualWeyl.Red.cM_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T09:59:22.382652+00:00
-- url     : https://prove2.me/submissions/e8cd3bdf-6b0d-4d32-944e-b11eca974f4c

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
theorem _root_.solution (g h : Matrix (Fin k) (Fin k) R) : cM (g * h) = cM g * cM h := by
  first
  | (unfold cM; exact Matrix.map_mul)
  | (ext i j; simp [cM, Matrix.mul_apply])
end PI.OddDualWeyl.Red
