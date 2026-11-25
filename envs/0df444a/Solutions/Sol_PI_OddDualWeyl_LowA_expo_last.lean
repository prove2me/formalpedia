-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.expo_last
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T09:59:19.105804+00:00
-- url     : https://prove2.me/submissions/a2b82a23-3287-445a-8481-9002ca7dd087

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
import Theorems.Thm_PI_OddDualWeyl_LowA_nuNext_last

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
open PI PI.OddDualWeyl PI.OddDualWeyl.LowA
variable {R : Type*} [CommRing R]
namespace PI.OddDualWeyl.LowA
theorem _root_.solution {m : ℕ} (lam : Fin (m + 1) → ℤ) :
    nuOf lam (Fin.last m) - nuNext (nuOf lam) (Fin.last m) = 0 := by
  rw [nuNext_last]
  simp [PI.OddDualWeyl.nuOf]
end PI.OddDualWeyl.LowA
