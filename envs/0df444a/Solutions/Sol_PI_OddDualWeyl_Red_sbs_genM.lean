-- Prove2me | solution 1 for PI.OddDualWeyl.Red.sbs_genM
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:11:26.919176+00:00
-- url     : https://prove2.me/submissions/5a85bbfe-0848-4454-a7fa-ec1c64c557d8

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
theorem _root_.solution (p : MvPolynomial (Fin k × Fin k) R) : sbs (genM R k) p = p := by
  have h : sbs (PI.OddDualWeyl.genM R k) = AlgHom.id R (MvPolynomial (Fin k × Fin k) R) := by
    apply MvPolynomial.algHom_ext
    intro v
    simp [sbs_X, PI.OddDualWeyl.genM]
  rw [h, AlgHom.id_apply]
end PI.OddDualWeyl.Red
