-- Prove2me | solution 1 for PI.OddDualWeyl.applyWord_cons
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:59:51.32515+00:00
-- url     : https://prove2.me/submissions/5c94d733-da6f-4e3e-8939-98743096b969

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
theorem _root_.solution (x : Fin k × Fin k × ℕ) (w : List (Fin k × Fin k × ℕ)) (f : MvPolynomial (Fin k × Fin k) R) :
    applyWord R (x :: w) f = rowDiv R x.1 x.2.1 x.2.2 (applyWord R w f) := rfl
end PI.OddDualWeyl
