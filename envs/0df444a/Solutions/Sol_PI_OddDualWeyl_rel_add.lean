-- Prove2me | solution 1 for PI.OddDualWeyl.rel_add
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:57:10.005068+00:00
-- url     : https://prove2.me/submissions/7dd554ef-3bf6-4a88-bf68-046e24315d29

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
theorem _root_.solution {f g f' g' : MvPolynomial (Fin k × Fin k) R} (h1 : Rel R k M f f') (h2 : Rel R k M g g') :
    Rel R k M (f + g) (f' + g') := by
  unfold Rel at *
  rw [map_add, h1, h2, mul_add]
end PI.OddDualWeyl
