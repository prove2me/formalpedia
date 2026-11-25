-- Prove2me | solution 1 for PI.OddDualWeyl.Red.cM_map
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T10:06:00.826564+00:00
-- url     : https://prove2.me/submissions/cde8d7ef-3fda-46a5-913c-97df1e506b5b

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_AevalMulHomog
import Theorems.Thm_PI_OddDualWeyl_Red_sbs_C

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
theorem _root_.solution (A : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R)) (g : Matrix (Fin k) (Fin k) R) :
    (cM g).map (sbs A) = cM g := by
  ext i j
  simp [cM, sbs_C]
end PI.OddDualWeyl.Red
