-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.Phi_symm_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:13:54.30389+00:00
-- url     : https://prove2.me/submissions/e1ed1e11-8036-4f3e-b297-587745b26100

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandC

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
theorem _root_.solution (c : (L ≃ₐ[K] L) → K) :
    (Phi K L).symm c = ∑ σ, c σ • σ (IsGalois.normalBasis K L 1) := by
  show (IsGalois.normalBasis K L).equivFun.symm c = _
  rw [Module.Basis.equivFun_symm_apply]
  exact Finset.sum_congr rfl fun σ _ => by rw [IsGalois.normalBasis_apply]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
