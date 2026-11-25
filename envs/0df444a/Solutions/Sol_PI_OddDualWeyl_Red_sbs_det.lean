-- Prove2me | solution 1 for PI.OddDualWeyl.Red.sbs_det
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T09:59:08.049654+00:00
-- url     : https://prove2.me/submissions/9ed8ca29-88a2-425a-9120-44fc4de7a238

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
theorem _root_.solution (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) :
    sbs A (genM R k).det = A.det := by
  first
  | simpa [RingHom.mapMatrix_apply, genM_map] using
      RingHom.map_det (sbs A).toRingHom (PI.OddDualWeyl.genM R k)
  | rw [AlgHom.map_det, AlgHom.mapMatrix_apply, genM_map]
end PI.OddDualWeyl.Red
