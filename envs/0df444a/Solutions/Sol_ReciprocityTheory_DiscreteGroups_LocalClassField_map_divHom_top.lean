-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.map_divHom_top
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:09:04.758536+00:00
-- url     : https://prove2.me/submissions/85481f81-8101-4048-8044-81202374e879

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsA
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh
noncomputable section
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (e : ℕ) : (⊤ : AddSubgroup ℤ).map (divHom e) = AddSubgroup.zmultiples ((e : ℝ)⁻¹) := by
  rw [← AddMonoidHom.range_eq_map, divHom, AddSubgroup.range_zmultiplesHom]
end ReciprocityTheory.DiscreteGroups.LocalClassField
