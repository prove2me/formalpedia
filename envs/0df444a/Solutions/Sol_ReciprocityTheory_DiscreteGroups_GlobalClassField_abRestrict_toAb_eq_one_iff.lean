-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.abRestrict_toAb_eq_one_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T20:16:34.679154+00:00
-- url     : https://prove2.me/submissions/f1fdeb99-6bf0-4ad4-8129-4e440b05b1e0

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
import Theorems.Thm_Neutral_B1_abRestrict_mk


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
theorem _root_.solution (h : IsFiniteAbelian F L) (g : AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :
    abRestrict F L h (toAb F g) = 1 ↔ g ∈ L.fixingSubgroup := by
  have := h.isGalois
  rw [abRestrict_mk, ← MonoidHom.mem_ker, IntermediateField.restrictNormalHom_ker]
end ReciprocityTheory.DiscreteGroups.GlobalClassField
