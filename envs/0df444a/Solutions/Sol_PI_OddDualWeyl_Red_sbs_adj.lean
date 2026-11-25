-- Prove2me | solution 1 for PI.OddDualWeyl.Red.sbs_adj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:02.693184+00:00
-- url     : https://prove2.me/submissions/39f74a90-b7a0-45ff-8945-c2e44d51eefd

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_genM_map

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
theorem _root_.solution (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (i j : Fin k) :
    sbs A ((genM R k).adjugate i j) = A.adjugate i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (sbs A).toRingHom (PI.OddDualWeyl.genM R k)) i) j
  simpa [RingHom.mapMatrix_apply, genM_map] using h
end PI.OddDualWeyl.Red
