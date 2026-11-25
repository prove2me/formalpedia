-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.vLayerMap_eq_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T17:08:06.412904+00:00
-- url     : https://prove2.me/submissions/8bf8f18f-f810-4bfb-9a09-a85391a625ee

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vLayerMap_spec

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
theorem _root_.solution (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal]
    (x : (layer p K L).V) : vLayerMap p K L x = 0 ↔ x ∈ LinearMap.range (layerUIncl p K L).u := by
  have he' : (eK p L : ℝ) ≠ 0 := by positivity
  rw [← Int.cast_inj (α := ℝ), vLayerMap_spec p h, Int.cast_zero, mul_eq_zero, or_iff_right he']
  constructor
  · intro hx
    exact ⟨⟨⟨x.1, hx⟩, fun g => Subtype.ext (x.2 g)⟩, Subtype.ext rfl⟩
  · rintro ⟨y, rfl⟩
    exact y.1.2
end ReciprocityTheory.DiscreteGroups.LocalClassField
