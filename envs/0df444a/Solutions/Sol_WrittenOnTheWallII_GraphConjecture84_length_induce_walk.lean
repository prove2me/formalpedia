-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.length_induce_walk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:32:37.447187+00:00
-- url     : https://prove2.me/submissions/927d2c51-224b-461a-8897-28d15b76da13

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
theorem _root_.solution {G : SimpleGraph α} {S : Set α} {u v : α}
    (p : G.Walk u v) (hp : ∀ z ∈ p.support, z ∈ S) :
    (p.induce S hp).length = p.length := by
  calc
    (p.induce S hp).length = ((p.induce S hp).map
        (SimpleGraph.Embedding.induce S).toHom).length := (Walk.length_map _ _).symm
    _ = p.length := congrArg Walk.length (Walk.map_induce p hp)
end WrittenOnTheWallII.GraphConjecture84
