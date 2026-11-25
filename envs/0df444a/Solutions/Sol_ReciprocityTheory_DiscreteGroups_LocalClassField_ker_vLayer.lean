-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.ker_vLayer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:23:06.715243+00:00
-- url     : https://prove2.me/submissions/2a2b09f0-7555-40cf-81dd-d722c54e57e2

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ExistsDvdQKPowSubOne
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsE
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_vLayerMap_eq_zero_iff

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
theorem _root_.solution (he : 0 < eK p L) (h : K ≤ L) [(subG p K L).Normal] :
    LinearMap.ker (vLayer p K L).u = LinearMap.range (layerUIncl p K L).u := by
  ext x
  rw [LinearMap.mem_ker]
  exact vLayerMap_eq_zero_iff p he h x
end ReciprocityTheory.DiscreteGroups.LocalClassField
