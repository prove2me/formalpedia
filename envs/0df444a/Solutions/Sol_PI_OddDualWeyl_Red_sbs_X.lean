-- Prove2me | solution 1 for PI.OddDualWeyl.Red.sbs_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:08.357782+00:00
-- url     : https://prove2.me/submissions/6288e1e6-59e2-45f6-baab-e1e1e0c1c34f

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
theorem _root_.solution (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (v : Fin k × Fin k) :
    sbs A (X v) = A v.1 v.2 := by
  first
  | simp [sbs]
  | exact aeval_X _ _
end PI.OddDualWeyl.Red
