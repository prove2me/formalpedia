-- Prove2me | solution 1 for PI.OddDualWeyl.Intw.rowGen_genM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:05:29.742916+00:00
-- url     : https://prove2.me/submissions/4390773a-39ee-461c-aca1-484cc1de83ba

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_TransvectionMulApply
import Theorems.Thm_PI_OddDualWeyl_Intw_transvection_mul_apply

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
open PI.OddDualWeyl.Intw
variable {R : Type} [CommRing R] {k : ℕ}
namespace PI.OddDualWeyl.Intw
theorem _root_.solution (a b : Fin k) :
    (rowGen R a b).toRingHom.mapMatrix (genM R k) =
      transvection b a (Polynomial.X) *
        (Polynomial.C : MvPolynomial (Fin k × Fin k) R →+* _).mapMatrix (genM R k) := by
  ext i s
  rw [transvection_mul_apply]
  simp [PI.OddDualWeyl.genM, PI.OddDualWeyl.rowGen]
end PI.OddDualWeyl.Intw
