-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_toLayer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:11:30.639624+00:00
-- url     : https://prove2.me/submissions/442944e9-30f9-4e87-b3ab-92a2267d1562

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_toLayer_val
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vLayerMap_spec
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vOn_spec


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
variable (p : ℕ) [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) [(subG p K L).Normal] (x : multOf p L) :
    vLayerMap p K L (toLayer p x) = vOn p L x := by
  apply Int.cast_injective (α := ℝ)
  rw [vLayerMap_spec p h, vOn_spec, toLayer_val]
end ReciprocityTheory.DiscreteGroups.LocalClassField
