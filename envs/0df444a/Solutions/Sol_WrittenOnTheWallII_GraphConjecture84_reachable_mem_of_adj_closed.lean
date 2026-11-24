-- Prove2me | solution 1 for WrittenOnTheWallII.GraphConjecture84.reachable_mem_of_adj_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:23:45.811549+00:00
-- url     : https://prove2.me/submissions/f16afe2d-ed8c-4157-bb72-eb8e3ea6831b

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
theorem _root_.solution {G : SimpleGraph α} {S : Set α}
    (hS : ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S) {u v : α}
    (hr : G.Reachable u v) (hu : u ∈ S) : v ∈ S := by
  obtain ⟨p⟩ := hr
  revert hu
  induction p with
  | nil => exact fun hu => hu
  | cons huv p ih => exact fun hu => ih (hS _ hu _ huv)
end WrittenOnTheWallII.GraphConjecture84
