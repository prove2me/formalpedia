-- Prove2me | solution 1 for PI.OddDualWeyl.rel_smul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:51.734268+00:00
-- url     : https://prove2.me/submissions/888b5676-e7f8-4537-9de6-9e6470b0c1bf

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
theorem _root_.solution {f f' : MvPolynomial (Fin k × Fin k) R} (c : R) (h : Rel R k M f f') :
    Rel R k M (c • f) (c • f') := by
  unfold Rel at *
  rw [map_smul, h, mul_smul_comm]
end PI.OddDualWeyl
