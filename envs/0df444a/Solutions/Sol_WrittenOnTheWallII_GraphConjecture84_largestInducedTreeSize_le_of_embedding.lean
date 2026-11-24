-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.largestInducedTreeSize_le_of_embedding
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:01.82218+00:00
-- url     : https://prove2.me/submissions/917b08b9-ac89-4f87-a4dc-efd913a8a726

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_SimpleGraph_card_le_largestInducedTreeSize


set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {β : Type*} [Fintype β] [DecidableEq β]
    {H : SimpleGraph β} {G : SimpleGraph α} (e : H ↪g G) :
    largestInducedTreeSize H ≤ largestInducedTreeSize G := by
  classical
  apply csSup_le'
  rintro n ⟨s, rfl, hs⟩
  let f : ↥(s : Set β) → ↥(s.map e.toEmbedding : Set α) := fun x =>
    ⟨e x, Finset.mem_map.mpr ⟨x, x.property, rfl⟩⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y hxy
      apply Subtype.ext
      exact e.injective (congrArg Subtype.val hxy)
    · intro y
      obtain ⟨x, hx, hxy⟩ := Finset.mem_map.mp y.property
      exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  let i : H.induce (s : Set β) ≃g G.induce (s.map e.toEmbedding : Set α) :=
    { Equiv.ofBijective f hf with
      map_rel_iff' := by intro x y; exact e.map_rel_iff }
  have htree := i.isTree_iff.mp hs
  simpa only [Finset.card_map] using card_le_largestInducedTreeSize htree
end WrittenOnTheWallII.GraphConjecture84
