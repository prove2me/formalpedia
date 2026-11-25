-- Prove2me | solution 1 for PI.OddDualWeyl.Uniq.dualM_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T09:58:05.001154+00:00
-- url     : https://prove2.me/submissions/cda3f3ac-9880-4b77-a172-b3adf2c021f7

import Mathlib
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_JacRev
import Definitions.Def_Lemmata_GeneralBFactRightAlt_Imports
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_OddDualWeylJacobian_HighestWeightVectorUnique
import Theorems.Thm_PI_OddDualWeyl_Uniq_mul_P

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
theorem _root_.solution : dualM Rg k = (adjugate (genM Rg k))ᵀ * P _ k := by
  rw [mul_P]; ext i j; simp [dualM]
end PI.OddDualWeyl.Uniq
