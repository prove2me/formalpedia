-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.toAb_surjective
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:49:06.398658+00:00
-- url     : https://prove2.me/submissions/235fde90-a3eb-49b1-802e-e6e1bffb94d5

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ReciprocityTheory ReciprocityTheory.DiscreteGroups ReciprocityTheory.DiscreteGroups.GlobalClassField
open _root_.Neutral.B1 Topology Function
open scoped commutatorElement
variable {F : Type*} [Field F] {L L' : IntermediateField F (AlgebraicClosure F)}
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution : Surjective (toAb F) := QuotientGroup.mk'_surjective _
end ReciprocityTheory.DiscreteGroups.GlobalClassField
