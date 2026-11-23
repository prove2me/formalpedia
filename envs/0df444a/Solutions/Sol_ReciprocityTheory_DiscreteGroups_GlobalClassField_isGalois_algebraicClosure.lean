-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isGalois_algebraicClosure
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:36.990556+00:00
-- url     : https://prove2.me/submissions/53e350d3-5e7f-41f5-9360-4c3eb836f0e1

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
theorem _root_.solution [CharZero F] : IsGalois F (AlgebraicClosure F) := ⟨⟩
end ReciprocityTheory.DiscreteGroups.GlobalClassField
