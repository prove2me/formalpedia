-- Prove2me | solution 1 for PI.OddDualWeyl.Red.sbs_C
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:58:56.735969+00:00
-- url     : https://prove2.me/submissions/7a0f0c0e-1bd5-4498-90b0-3debae6261bc

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
theorem _root_.solution (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (r : R) :
    sbs A (C r) = C r := by
  first
  | simp [sbs]
  | rw [sbs, aeval_C, algebraMap_eq]
end PI.OddDualWeyl.Red
