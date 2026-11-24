-- Prove2me | solution 1 for PI.OddDualWeyl.LowA.nuStar_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T06:04:46.705998+00:00
-- url     : https://prove2.me/submissions/7b3d9ce3-162d-4644-8c2e-e80296a2c1b7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_MnrUpdateEqZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightDualOf

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
theorem _root_.solution {m : ℕ} (lam : Fin (m + 1) → ℤ) (t : Fin (m + 1)) :
    nuOf (lamStar lam) t = (lam 0 - lam t.rev).toNat := by
  simp only [PI.OddDualWeyl.nuOf, PI.OddDualWeyl.lamStar, Fin.rev_last]
  congr 1
  ring
end PI.OddDualWeyl.LowA
