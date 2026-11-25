-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.smulHom_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T10:48:33.286185+00:00
-- url     : https://prove2.me/submissions/9ff04d5a-df6f-4aad-9bb6-71daeb2827fe

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_Development
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_RelIdxNeZeroOfLeLeft
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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]
namespace PI.UnitaryGroupMassFormula.UnimodLocStd
theorem _root_.solution {w : ℂ} (hw : w ≠ 0) : Function.Injective (smulHom (V := V) w) := by
  intro x y hxy
  simp only [smulHom_apply] at hxy
  have h := congrArg (fun v => w⁻¹ • v) hxy
  simpa [smul_smul, inv_mul_cancel₀ hw] using h
end PI.UnitaryGroupMassFormula.UnimodLocStd
