-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.mem_imgLat_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T22:23:23.327812+00:00
-- url     : https://prove2.me/submissions/2cedd739-262d-4ec6-83fd-483b18974c9f

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
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
theorem _root_.solution (g : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) (x : V) :
    x ∈ imgLat (g : V →ₗ[ℂ] V) Λ ↔ ∃ y ∈ Λ, g y = x := by
  simp [imgLat, AddSubgroup.mem_map]
end PI.UnitaryGroupMassFormula.UnimodLocStd
