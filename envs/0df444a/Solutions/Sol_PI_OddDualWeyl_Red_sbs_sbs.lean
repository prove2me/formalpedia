-- Prove2me | solution 1 for PI.OddDualWeyl.Red.sbs_sbs
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:47.198632+00:00
-- url     : https://prove2.me/submissions/da50af2d-9a4d-467e-85a1-cc66969a0ac3

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
theorem _root_.solution (A B : Matrix (Fin k) (Fin k) (MvPolynomial (Fin k × Fin k) R))
    (p : MvPolynomial (Fin k × Fin k) R) : sbs A (sbs B p) = sbs (B.map (sbs A)) p := by
  have h : (sbs A).comp (sbs B) = sbs (B.map (sbs A)) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [sbs_X]
  simpa using DFunLike.congr_fun h p
end PI.OddDualWeyl.Red
