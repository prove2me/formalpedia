-- Prove2me | solution 1 for SimpleGraph.ramseyBound_one_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:25:56.554004+00:00
-- url     : https://prove2.me/submissions/fdad64cf-eb54-4c5e-9243-406f3ff17bf3

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
theorem _root_.solution (hn : 0 < n) (s : ℕ) : RamseyBound n 1 s := fun _ =>
  .inl ⟨{⟨0, hn⟩}, by simp⟩
end SimpleGraph
