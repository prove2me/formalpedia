-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.core_reachable_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:29:44.707668+00:00
-- url     : https://prove2.me/submissions/429c8793-8c73-4935-b1f9-ce9a18ebbedf

module
public import Mathlib
public import Definitions.Def_Wowii84_LargestInducedTree
public import Definitions.Def_Wowii84_Main
public import Theorems.Thm_WrittenOnTheWallII_GraphConjecture84_exists_walk_in_core_avoiding

set_option autoImplicit false
@[expose] public section
public section
open WrittenOnTheWallII WrittenOnTheWallII.GraphConjecture84
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace WrittenOnTheWallII.GraphConjecture84
theorem _root_.solution {G : SimpleGraph α} (K : Finset α)
    (hK : (G.induce (K : Set α)).Connected)
    (hdel : ∀ x : ↥(K : Set α),
      ((G.induce (K : Set α)).induce ({x}ᶜ : Set ↥(K : Set α))).Connected)
    (c : α) {u v : α} (hu : u ∈ K) (hv : v ∈ K) (huc : u ≠ c) (hvc : v ≠ c) :
    (G.induce ({c}ᶜ : Set α)).Reachable ⟨u, by simpa using huc⟩
      ⟨v, by simpa using hvc⟩ := by
  obtain ⟨p, _, hpc⟩ := exists_walk_in_core_avoiding K hK hdel c hu hv huc hvc
  exact ⟨p.induce ({c}ᶜ : Set α) (by
    intro z hz
    exact show z ≠ c from fun heq => hpc (heq ▸ hz))⟩
end WrittenOnTheWallII.GraphConjecture84
