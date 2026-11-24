-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isK_int
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T22:06:07.35887+00:00
-- url     : https://prove2.me/submissions/431e4c54-3ac9-4727-a3e2-9a5be23d1ae0

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
theorem _root_.solution (n : ℤ) : IsK b d n := by
  unfold PI.UnitaryGroupMassFormula.UnimodLocStd.IsK
  exact ⟨n, 0, 1, one_ne_zero, by simp⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
