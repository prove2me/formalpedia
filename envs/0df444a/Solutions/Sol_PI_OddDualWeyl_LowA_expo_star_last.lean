-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.expo_star_last
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:11:38.527793+00:00
-- url     : https://prove2.me/submissions/b6d2e037-26f1-4837-a9e4-8945d9841eb6

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf
import Theorems.Thm_PI_OddDualWeyl_LowA_nuNext_last
import Theorems.Thm_PI_OddDualWeyl_LowA_nuStar_apply

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
    nuOf (lamStar lam) (Fin.last m) - nuNext (nuOf (lamStar lam)) (Fin.last m) = 0 := by
  rw [nuNext_last, nuStar_apply, Fin.rev_last]
  simp
end PI.OddDualWeyl.LowA
