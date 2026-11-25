-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.sum_proj1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T13:58:49.243745+00:00
-- url     : https://prove2.me/submissions/cf1dc104-0d0d-4f17-ace8-9e62795201bf

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Phi_symm_apply
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_Phi_map

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
theorem _root_.solution (x : L) : ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x) = x := by
  calc ∑ σ : L ≃ₐ[K] L, σ • proj1 K L (σ⁻¹ • x)
      = ∑ σ : L ≃ₐ[K] L, Phi K L x σ • σ (IsGalois.normalBasis K L 1) := by
        refine Finset.sum_congr rfl fun σ _ => ?_
        show σ (Phi K L (σ⁻¹ x) 1 • IsGalois.normalBasis K L 1) = _
        rw [map_smul, Phi_map, inv_inv, mul_one]
    _ = x := by rw [← Phi_symm_apply, ContinuousLinearEquiv.symm_apply_apply]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
