-- Prove2me | solution 1 for PI.UnitaryGroupMassFormula.UnimodLocStd.isom_trans
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T10:45:37.836275+00:00
-- url     : https://prove2.me/submissions/1e6bbf50-c5a9-4443-9a2f-d0738d3620ec

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
theorem _root_.solution (H : Sesq V) (g σ : V ≃ₗ[ℂ] V) (hg : IsIsom H H (g : V →ₗ[ℂ] V)) (hσ : IsIsom H H (σ : V →ₗ[ℂ] V)) :
    IsIsom H H ((g.trans σ : V ≃ₗ[ℂ] V) : V →ₗ[ℂ] V) := by
  intro x y
  have h1 := hσ (g x) (g y)
  have h2 := hg x y
  simp only [LinearEquiv.coe_coe] at h1 h2 ⊢
  rw [LinearEquiv.trans_apply, LinearEquiv.trans_apply, h1, h2]
end PI.UnitaryGroupMassFormula.UnimodLocStd
