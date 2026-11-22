-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.kill
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:17:24.452367+00:00
-- url     : https://prove2.me/submissions/04d1ffcb-9b52-40b8-b3e2-96bb767a2067

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open PI PI.WeylForKWork PI.WeylForKWork.DimensionInduction
open scoped InnerProductSpace
open Module
variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {ι κ : Type*}
variable {ρ : ι → H →L[ℂ] H} {ρ' : κ → H →L[ℂ] H}
namespace PI.WeylForKWork.DimensionInduction
theorem _root_.solution {c : H →ₗ[ℂ] H} (hc : Comm ρ c) {X : Submodule ℂ H} (hXs : Stab ρ X) (hXi : Irr ρ X)
    {x₁ : H} (hx₁ : x₁ ∈ X) (h0 : x₁ ≠ 0) (hk : c x₁ = 0) : ∀ x ∈ X, c x = 0 := by
  have hst : Stab ρ (LinearMap.ker c ⊓ X) := by
    intro i v hv
    refine ⟨?_, hXs i v hv.2⟩
    show c (ρ i v) = 0
    rw [hc i v, LinearMap.mem_ker.1 hv.1, map_zero]
  rcases hXi _ inf_le_right hst with h | h
  · exfalso
    have hm : x₁ ∈ LinearMap.ker c ⊓ X := ⟨LinearMap.mem_ker.2 hk, hx₁⟩
    rw [h] at hm
    exact h0 ((Submodule.mem_bot ℂ).1 hm)
  · intro x hx
    rw [← h] at hx
    exact LinearMap.mem_ker.1 hx.1
end PI.WeylForKWork.DimensionInduction
