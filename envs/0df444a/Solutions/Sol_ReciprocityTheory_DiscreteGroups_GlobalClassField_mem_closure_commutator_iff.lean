-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.mem_closure_commutator_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T14:00:53.631801+00:00
-- url     : https://prove2.me/submissions/835e81f8-b326-483d-9a9d-7a878feb9e9d

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_abRestrict_toAb_eq_one_iff
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isGalois_algebraicClosure
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isFiniteAbelian_of_commutator_le

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
theorem _root_.solution [CharZero F] (g : Field.absoluteGaloisGroup F) :
    g ∈ (commutator (Field.absoluteGaloisGroup F)).topologicalClosure ↔
      ∀ L : IntermediateField F (AlgebraicClosure F), IsFiniteAbelian F L → g ∈ L.fixingSubgroup := by
  have := isGalois_algebraicClosure (F := F)
  constructor
  · intro hg L hL
    have h1 : toAb F g = 1 := (QuotientGroup.eq_one_iff g).2 hg
    exact (abRestrict_toAb_eq_one_iff hL g).1 (by rw [h1, map_one])
  · intro hg
    let C : ClosedSubgroup (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) :=
      ⟨(commutator (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F)).topologicalClosure,
        Subgroup.isClosed_topologicalClosure _⟩
    have hC : (IntermediateField.fixedField C.1).fixingSubgroup = C.1 :=
      InfiniteGalois.fixingSubgroup_fixedField C
    show g ∈ C.1
    rw [← hC]
    refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => ?_
    have hint : IsIntegral F x := Algebra.IsIntegral.isIntegral x
    have hfd : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
      IntermediateField.adjoin.finiteDimensional hint
    have hle : IntermediateField.adjoin F {x} ≤ IntermediateField.fixedField C.1 :=
      IntermediateField.adjoin_le_iff.2 (Set.singleton_subset_iff.2 hx)
    have hab : IsFiniteAbelian F (IntermediateField.adjoin F {x}) := by
      refine isFiniteAbelian_of_commutator_le hfd ?_
      refine le_trans ?_ (IntermediateField.fixingSubgroup_le hle)
      rw [hC]
      exact Subgroup.le_topologicalClosure _
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 (hg _ hab) x
      (IntermediateField.mem_adjoin_simple_self F x)
end ReciprocityTheory.DiscreteGroups.GlobalClassField
