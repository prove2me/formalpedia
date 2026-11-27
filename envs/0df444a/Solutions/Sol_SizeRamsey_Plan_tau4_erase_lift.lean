-- Prove2me | solution 1 for SizeRamsey.Plan.tau4_erase_lift
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:39.222818+00:00
-- url     : https://prove2.me/submissions/7442d011-1f5f-49c3-a677-e14008df2f2b

module
public import Definitions.Def_SizeRamsey_Basic
public import Definitions.Def_SizeRamsey_Deletion
public import Theorems.Thm_SizeRamsey_Plan_IsC4Map_erase_mk

set_option autoImplicit false
@[expose] public section
public section
open SizeRamsey SizeRamsey.Plan
open scoped BigOperators
universe u v
attribute [local instance] Classical.propDecidable
variable {V : Type*} [Fintype V] (G : SimpleGraph V)
namespace SizeRamsey.Plan
theorem _root_.solution
    (D X : Finset V) (hX : X ⊆ D)
    (hHit : HitsDeleted G D X)
    (T : Finset {v : V // v ∉ D})
    (hT : c4Transversal (erase G D) T) :
    c4Transversal G (liftTransversal D X T) ∧
      (liftTransversal D X T).card ≤ T.card + X.card := by
  clear hX
  refine ⟨fun f hf => ?_, ?_⟩
  · by_cases hD : ∃ i, f i ∈ D
    · obtain ⟨i, hi⟩ := hHit f hf hD
      exact ⟨i, Finset.mem_union_right _ hi⟩
    · push Not at hD
      obtain ⟨i, hi⟩ := hT _ (IsC4Map.erase_mk hf hD)
      exact ⟨i, Finset.mem_union_left _ (Finset.mem_image_of_mem Subtype.val hi)⟩
  · unfold liftTransversal
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add_right Finset.card_image_le _)
end SizeRamsey.Plan
