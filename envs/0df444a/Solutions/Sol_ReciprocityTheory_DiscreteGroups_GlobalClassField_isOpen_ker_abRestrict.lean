-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isOpen_ker_abRestrict
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:58.023199+00:00
-- url     : https://prove2.me/submissions/1a520959-ae7f-4960-8d28-ca30e27bf101

import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLimB
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_abRestrict_toAb_eq_one_iff


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
variable {F : Type*} [Field F] {L : IntermediateField F (AlgebraicClosure F)}
namespace ReciprocityTheory.DiscreteGroups.GlobalClassField
theorem _root_.solution (h : IsFiniteAbelian F L) :
    IsOpen ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F)) := by
  have := h.finiteDimensional
  have hq : IsOpen ((toAb F) ⁻¹' ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F))) := by
    have e : (toAb F) ⁻¹' ((abRestrict F L h).ker : Set (Field.absoluteGaloisGroupAbelianization F)) =
        ((L.fixingSubgroup : Subgroup Gal(AlgebraicClosure F/F)) : Set Gal(AlgebraicClosure F/F)) := by
      ext g
      exact abRestrict_toAb_eq_one_iff h g
    rw [e]
    exact L.fixingSubgroup_isOpen
  exact ((QuotientGroup.isQuotientMap_mk _).isOpen_preimage).1 hq
end ReciprocityTheory.DiscreteGroups.GlobalClassField
