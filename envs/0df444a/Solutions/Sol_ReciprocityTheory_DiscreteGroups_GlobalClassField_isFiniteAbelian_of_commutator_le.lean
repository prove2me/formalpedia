-- Prove2me | solution 1 for ReciprocityTheory.DiscreteGroups.GlobalClassField.isFiniteAbelian_of_commutator_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T13:48:52.242495+00:00
-- url     : https://prove2.me/submissions/94c0b724-953f-485a-ad34-ba6ce86b7099

import Mathlib
import Definitions.Def_ReciprocityTheory_NeutralLocalFields_Reciprocity
import Definitions.Def_ReciprocityTheory_ClassFieldTheory_GlobalClassField_AsGabLim
import Theorems.Thm_ReciprocityTheory_DiscreteGroups_GlobalClassField_isGalois_algebraicClosure

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
theorem _root_.solution [CharZero F] (hfd : FiniteDimensional F L)
    (hc : commutator (AlgebraicClosure F ≃ₐ[F] AlgebraicClosure F) ≤ L.fixingSubgroup) :
    IsFiniteAbelian F L := by
  have := isGalois_algebraicClosure (F := F)
  have hn : L.fixingSubgroup.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have h1 : g * n * g⁻¹ = ⁅g, n⁆ * n := by
      rw [commutatorElement_def]; group
    rw [h1]
    exact mul_mem (hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top n))) hn
  have hG : IsGalois F L := (InfiniteGalois.normal_iff_isGalois L).1 hn
  refine ⟨hfd, hG, fun a b => ?_⟩
  obtain ⟨g, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (AlgebraicClosure F) a
  obtain ⟨k, rfl⟩ := AlgEquiv.restrictNormalHom_surjective (F := F) (K₁ := L) (AlgebraicClosure F) b
  have h2 : ⁅g, k⁆ ∈ (AlgEquiv.restrictNormalHom (F := F) (K₁ := AlgebraicClosure F) L).ker := by
    rw [IntermediateField.restrictNormalHom_ker]
    exact hc (Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top k))
  rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h2
  exact h2
end ReciprocityTheory.DiscreteGroups.GlobalClassField
