-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.norm_Phi_proj1
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T14:12:17.12587+00:00
-- url     : https://prove2.me/submissions/51dfd7b0-986f-4760-a03d-ecbcb545d793

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
theorem _root_.solution (x : L) : ‖Phi K L (proj1 K L x)‖ ≤ ‖Phi K L x‖ := by
  classical
  rw [pi_norm_le_iff_of_nonneg (norm_nonneg _)]
  intro τ
  show ‖Phi K L (Phi K L x 1 • IsGalois.normalBasis K L 1) τ‖ ≤ _
  rw [map_smul, Pi.smul_apply]
  have : Phi K L (IsGalois.normalBasis K L 1) τ = if 1 = τ then 1 else 0 :=
    Module.Basis.equivFun_self _ _ _
  rw [this, smul_eq_mul]
  split_ifs
  · rw [mul_one]; exact norm_le_pi_norm _ _
  · rw [mul_zero, norm_zero]; exact norm_nonneg _
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
