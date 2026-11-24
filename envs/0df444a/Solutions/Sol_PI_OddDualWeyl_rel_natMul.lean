-- Prove2me | solution 1 for PI.OddDualWeyl.rel_natMul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:51.627201+00:00
-- url     : https://prove2.me/submissions/461dc159-2375-4935-9131-fa16a29c51f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_RevColOneTranspose

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
open PI PI.OddDualWeyl
variable {R : Type} [CommRing R] {k M : ℕ}
namespace PI.OddDualWeyl
theorem _root_.solution {f f' : MvPolynomial (Fin k × Fin k) R} (n : ℕ) (h : Rel R k M f f') :
    Rel R k M ((n : MvPolynomial (Fin k × Fin k) R) * f) ((n : MvPolynomial (Fin k × Fin k) R) * f') := by
  unfold Rel at *
  rw [map_mul, map_natCast, h]
  ring
end PI.OddDualWeyl
