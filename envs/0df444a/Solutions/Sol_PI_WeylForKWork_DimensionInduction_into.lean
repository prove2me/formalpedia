-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.into
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:56.088476+00:00
-- url     : https://prove2.me/submissions/8cbfa7f1-89ea-4a6f-8014-ffe422620b8a

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_proj_comm
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_comm_comp
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_kill
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork PI.WeylForKWork.DimensionInduction
open scoped InnerProductSpace
open Module
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}
variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}
namespace PI.WeylForKWork.DimensionInduction
theorem _root_.solution (hρ : Good ρ) {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X W : Submodule ℂ H} [FiniteDimensional ℂ W]
    (hW : Stab ρ W) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0)
    (hin : c x₁ ∈ W) : ∀ x ∈ X, c x ∈ W := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hd : Comm ρ (c - P ∘ₗ c) :=
    (commSub ρ).sub_mem hc (comm_comp (proj_comm hρ hW) hc)
  have h1 : (c - P ∘ₗ c) x₁ = 0 := by
    simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
      Submodule.starProjection_eq_self_iff.2 hin, sub_self]
  intro x hx
  have h2 := kill hd hXs hXi hx₁ h0 h1 x hx
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe,
    sub_eq_zero] at h2
  rw [h2]
  exact (W.orthogonalProjection (c x)).2
end PI.WeylForKWork.DimensionInduction
