-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt.normU_val
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T17:12:48.379801+00:00
-- url     : https://prove2.me/submissions/af81b550-0fd6-4e64-bf18-4359749862db

import Mathlib
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_UnitsHerbrandB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_UnitsFilt_act_val

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
variable {R : Type*} [Field R] {G : Type*} [Group G] [Fintype G] [MulSemiringAction G R]
namespace ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
theorem _root_.solution (u : Rˣ) : ((normU G u : Rˣ) : R) = ∏ g : G, g • (u : R) := by
  simp [normU, Units.coe_prod, act_val]
end ReciprocityTheory.DiscreteGroups.LocalClassField.UnitsFilt
