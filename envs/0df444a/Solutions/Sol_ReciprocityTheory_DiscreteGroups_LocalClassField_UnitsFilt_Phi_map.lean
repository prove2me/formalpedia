-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Phi_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:17:31.989749+00:00
-- url     : https://prove2.me/submissions/56b6594c-39ce-44a8-979e-1ba8cf42451a

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Phi_symm_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
open Finset
variable (K L : Type*) [NontriviallyNormedField K] [CompleteSpace K] [IsUltrametricDist K] [NormedField L]
  [NormedAlgebra K L] [FiniteDimensional K L] [IsGalois K L]
variable {K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
theorem _root_.solution (σ : L ≃ₐ[K] L) (x : L) (τ : L ≃ₐ[K] L) : Phi K L (σ x) τ = Phi K L x (σ⁻¹ * τ) := by
  have : σ x = (Phi K L).symm (fun τ => Phi K L x (σ⁻¹ * τ)) := by
    rw [Phi_symm_apply]
    calc σ x = σ ((Phi K L).symm (Phi K L x)) := by simp
      _ = ∑ ρ, Phi K L x ρ • (σ * ρ) (IsGalois.normalBasis K L 1) := by
        rw [Phi_symm_apply, map_sum]
        exact Finset.sum_congr rfl fun ρ _ => by rw [map_smul]; rfl
      _ = ∑ τ, Phi K L x (σ⁻¹ * τ) • τ (IsGalois.normalBasis K L 1) :=
        Fintype.sum_equiv (Equiv.mulLeft σ) _ _ (fun ρ => by simp)
  rw [this, ContinuousLinearEquiv.apply_symm_apply]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
