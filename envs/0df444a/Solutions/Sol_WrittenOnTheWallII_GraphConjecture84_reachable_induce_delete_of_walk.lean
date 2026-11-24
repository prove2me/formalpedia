-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.reachable_induce_delete_of_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:33:51.304339+00:00
-- url     : https://prove2.me/submissions/cc8db0d4-adfc-4e80-a2eb-d50c7bf2d002

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} {S : Set α} (x : S)
    (u v : ↥({x}ᶜ : Set S)) (p : G.Walk ((u : S) : α) ((v : S) : α))
    (hS : ∀ z ∈ p.support, z ∈ S) (hx : (x : α) ∉ p.support) :
    ((G.induce S).induce ({x}ᶜ : Set S)).Reachable u v := by
  let T : Set α := {z | z ∈ S ∧ z ≠ (x : α)}
  have hT : ∀ z ∈ p.support, z ∈ T := by
    intro z hz
    exact ⟨hS z hz, fun hzx => hx (hzx ▸ hz)⟩
  let f : G.induce T →g (G.induce S).induce ({x}ᶜ : Set S) :=
    { toFun := fun z => ⟨⟨z, z.property.1⟩, by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro heq
        exact z.property.2 (congrArg Subtype.val heq)⟩
      map_rel' := by intro u v huv; exact huv }
  exact ⟨(p.induce T hT).map f⟩
end WrittenOnTheWallII.GraphConjecture84
