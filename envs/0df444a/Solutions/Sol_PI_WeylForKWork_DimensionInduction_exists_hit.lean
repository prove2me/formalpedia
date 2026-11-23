-- Prove2me | solution 1 for PI.WeylForKWork.DimensionInduction.exists_hit
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:56.111714+00:00
-- url     : https://prove2.me/submissions/ba8452f6-9aa0-49bb-ad58-b29be26f0bcd

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_FormulaStep
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_WeylFormulaCompact_DimStepA
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_proj_comm
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_comm_comp
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_kill
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_stab_map
import Theorems.Thm_PI_WeylForKWork_DimensionInduction_stab_iSup
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
theorem _root_.solution (hρ : Good ρ) (hρ' : Good ρ') (hcomm : ∀ i j v, ρ i (ρ' j v) = ρ' j (ρ i v))
    {S X W : Submodule ℂ H} (hSρ' : Stab ρ' S)
    (hSirr : ∀ S' : Submodule ℂ H, S' ≤ S → Stab ρ S' → Stab ρ' S' → S' = ⊥ ∨ S' = S)
    (hXS : X ≤ S) (hXs : Stab ρ X) (hXi : Irr ρ X) {x₀ : H} (hx₀ : x₀ ∈ X) (h0 : x₀ ≠ 0)
    [FiniteDimensional ℂ W] (hWS : W ≤ S) (hW0 : W ≠ ⊥) (hWs : Stab ρ W) :
    ∃ c : H →ₗ[ℂ] H, Comm ρ c ∧ c x₀ ∈ W ∧ c x₀ ≠ 0 := by
  set P : H →ₗ[ℂ] H := (W.starProjection : H →ₗ[ℂ] H) with hP
  have hPc : Comm ρ P := proj_comm hρ hWs
  have hρ'c : ∀ j, Comm ρ (ρ' j : H →ₗ[ℂ] H) := fun j i v => (hcomm i j v).symm
  by_contra hne
  push_neg at hne
  have hzero : ∀ j, ∀ x ∈ X, P (ρ' j x) = 0 := by
    intro j
    have hcj : Comm ρ (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) := comm_comp hPc (hρ'c j)
    have hk : (P ∘ₗ (ρ' j : H →ₗ[ℂ] H)) x₀ = 0 := by
      refine hne _ hcj ?_
      simp only [LinearMap.comp_apply, hP, ContinuousLinearMap.coe_coe]
      exact (W.orthogonalProjection _).2
    exact kill hcj hXs hXi hx₀ h0 hk
  set T : Submodule ℂ H := ⨆ j, X.map (ρ' j : H →ₗ[ℂ] H) with hT
  have hTρ : Stab ρ T := stab_iSup fun j => stab_map (hρ'c j) hXs
  have hTρ' : Stab ρ' T := by
    intro j' v hv
    have hle : T ≤ T.comap (ρ' j' : H →ₗ[ℂ] H) := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hρ'.mul j' j
      show ρ' j' (ρ' j x) ∈ T
      rw [hk x]
      exact Submodule.mem_iSup_of_mem k ⟨x, hx, rfl⟩
    exact hle hv
  have hTS : T ≤ S := by
    refine iSup_le fun j => ?_
    rintro _ ⟨x, hx, rfl⟩
    exact hSρ' j x (hXS hx)
  have hx₀T : x₀ ∈ T := by
    obtain ⟨o, ho⟩ := hρ'.one
    have hm : ρ' o x₀ ∈ T := Submodule.mem_iSup_of_mem o ⟨x₀, hx₀, rfl⟩
    rwa [ho] at hm
  rcases hSirr T hTS hTρ hTρ' with h | h
  · rw [h] at hx₀T
    exact h0 ((Submodule.mem_bot ℂ).1 hx₀T)
  · have hle : T ≤ LinearMap.ker P := by
      refine iSup_le fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact LinearMap.mem_ker.2 (hzero j x hx)
    apply hW0
    rw [eq_bot_iff]
    intro w hw
    have hwT : w ∈ T := by
      rw [h]
      exact hWS hw
    have h1 : P w = 0 := LinearMap.mem_ker.1 (hle hwT)
    have h2 : P w = w := by
      simp only [hP, ContinuousLinearMap.coe_coe]
      exact Submodule.starProjection_eq_self_iff.2 hw
    refine (Submodule.mem_bot ℂ).2 ?_
    rw [← h2]
    exact h1
end PI.WeylForKWork.DimensionInduction
