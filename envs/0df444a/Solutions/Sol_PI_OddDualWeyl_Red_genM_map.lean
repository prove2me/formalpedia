-- Prove2me | solution 1 for PI.OddDualWeyl.Red.genM_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:40:46.1625+00:00
-- url     : https://prove2.me/submissions/7c140240-20b3-49f8-94de-9bd676f38712

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_sbs_X

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
    (genM R k).map (sbs A) = A := by
  ext i j
  simp [PI.OddDualWeyl.genM, sbs_X]
end PI.OddDualWeyl.Red
