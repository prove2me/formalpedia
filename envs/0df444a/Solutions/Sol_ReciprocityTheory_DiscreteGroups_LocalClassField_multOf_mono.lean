-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.multOf_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T14:09:44.776967+00:00
-- url     : https://prove2.me/submissions/ba2ecd64-68f7-493b-a11b-402113510239

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsB
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC

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
theorem _root_.solution (h : K ≤ L) : multOf p K ≤ multOf p L := fun _ hx => h hx
end ReciprocityTheory.DiscreteGroups.LocalClassField
