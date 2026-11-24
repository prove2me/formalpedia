-- Prove2me | solution 1 for PI.OddDualWeyl.Red.map_mul_sbs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:08.550152+00:00
-- url     : https://prove2.me/submissions/1381d99e-92e0-4cdd-ad0f-22792139d2ac

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
theorem _root_.solution (A M N : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    (M * N).map (sbs A) = M.map (sbs A) * N.map (sbs A) := by
  ext i j
  simp [Matrix.mul_apply, _root_.map_sum, _root_.map_mul]
end PI.OddDualWeyl.Red
