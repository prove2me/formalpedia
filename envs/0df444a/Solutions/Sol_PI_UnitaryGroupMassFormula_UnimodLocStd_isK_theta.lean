-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T10:47:24.701032+00:00
-- url     : https://prove2.me/submissions/ce96d607-d4ff-4bc8-b583-88b3b49a816e

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_SelfDualStd
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_IsKTheta
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_smulHom_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_apply



set_option autoImplicit false
noncomputable section
open scoped ComplexConjugate
open PI PI.UnitaryGroupMassFormula PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS
variable (b : ℤ) (d : ℕ)
variable {b d}
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution : IsK b d (cmTheta b d) := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨0, 1, 1, one_ne_zero, by simp⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
