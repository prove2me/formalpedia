-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.LocalClassField.isScalarTower_zp_K_alg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T17:00:23.764789+00:00
-- url     : https://prove2.me/submissions/f97c98ab-7a0b-4bf5-952d-2662e34f17da

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsC
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_LocalFieldComparison_LocalFieldAutomorphisms_ModelF
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_LocalClassField_ValUnitsD

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.LocalClassField
open _root_.Neutral.B1 ReciprocityTheory.Coh ReciprocityTheory.Neutral.Cmp
noncomputable section
variable (p : ℕ) [Fact p.Prime] (K L : IntermediateField ℚ_[p] (PadicAlgCl p))
attribute [local instance] zpAlgOK
namespace ReciprocityTheory.DiscreteGroups.LocalClassField
theorem _root_.solution : IsScalarTower ℤ_[p] K (PadicAlgCl p) := IsScalarTower.of_algebraMap_eq fun _ => rfl
end ReciprocityTheory.DiscreteGroups.LocalClassField
