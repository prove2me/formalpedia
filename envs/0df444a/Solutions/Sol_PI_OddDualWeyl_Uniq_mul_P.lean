-- Prove2me | solution 1 for PI.OddDualWeyl.Uniq.mul_P
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T05:32:08.73161+00:00
-- url     : https://prove2.me/submissions/976f1f9f-ee9a-4528-affe-046b0ff73cd1

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique

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
open PI PI.OddDualWeyl PI.OddDualWeyl.Uniq
variable {Rg : Type*} [CommRing Rg] {k : ℕ}
namespace PI.OddDualWeyl.Uniq
theorem _root_.solution (B : Matrix (Fin k) (Fin k) Rg) : B * P Rg k = Matrix.of fun i j => B i (Fin.rev j) := by
  ext i j; simp [P, Matrix.mul_apply]
end PI.OddDualWeyl.Uniq
