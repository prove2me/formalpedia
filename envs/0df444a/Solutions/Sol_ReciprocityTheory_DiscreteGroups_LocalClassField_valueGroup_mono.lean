-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.valueGroup_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T14:26:21.771136+00:00
-- url     : https://prove2.me/submissions/5cb7260b-1354-4505-a065-3fc4ca5658ed

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_LocalClassField_multOf_mono

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
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
variable {K L}
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution (h : K ≤ L) : valueGroup p K ≤ valueGroup p L := AddSubgroup.map_mono (multOf_mono p h)
end ReciprocityTheory.DiscreteGroups.LocalClassField
