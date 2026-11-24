-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.connected_induce_cutSide
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:30:53.178863+00:00
-- url     : https://prove2.me/submissions/db19d470-c81a-4d8b-927c-e8301a8bd050

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_geodesic_support_subset_cutSide

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (hG : G.Connected)
    (c : α) (a : ↥({c}ᶜ : Set α)) : (G.induce (cutSide G c a)).Connected := by
  rw [connected_iff_exists_forall_reachable]
  refine ⟨⟨c, Or.inl rfl⟩, ?_⟩
  intro v
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist c v
  exact ⟨p.induce (cutSide G c a) (geodesic_support_subset_cutSide hG a v.property p hp)⟩
end WrittenOnTheWallII.GraphConjecture84
