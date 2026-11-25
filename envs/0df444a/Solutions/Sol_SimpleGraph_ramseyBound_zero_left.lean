-- Prove2me | solution 1 for SimpleGraph.ramseyBound_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:25:54.941424+00:00
-- url     : https://prove2.me/submissions/267426f4-45b8-43e0-892a-aea940163d57

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}
namespace SimpleGraph
theorem _root_.solution (n s : ℕ) : RamseyBound n 0 s := fun _ => .inl ⟨∅, by simp⟩
end SimpleGraph
