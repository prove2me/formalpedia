-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.imgLat_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:56:40.604343+00:00
-- url     : https://prove2.me/submissions/9d5999e4-393d-4108-b2e2-b5cc40e6ed62

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_CommOfBounded
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_QequivApply
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_KeyDef
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_UnimodularLocalStandard_ExistsGoodForm
import Theorems.Thm_PI_UnitaryGroupMassFormula_UnimodLocStd_mem_imgLat_iff
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
theorem _root_.solution (g σ : V ≃ₗ[ℂ] V) (Λ : AddSubgroup V) :
    imgLat ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) Λ = imgLat (σ : V →ₗ[ℂ] V) (imgLat (g : V →ₗ[ℂ] V) Λ) := by
  ext x
  simp only [mem_imgLat_iff]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨g y, ⟨y, hy, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨y, hy, rfl⟩
end PI.UnitaryGroupMassFormula.UnimodLocStd
