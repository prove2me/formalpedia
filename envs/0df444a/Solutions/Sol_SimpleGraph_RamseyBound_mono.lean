-- Prove2me | solution 1 for SimpleGraph.RamseyBound.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:57.30462+00:00
-- url     : https://prove2.me/submissions/09e16a6b-8559-47ba-9d23-f75f2b2cac3f

module
public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Definitions.Def_RamseyReservoir_RamseyBound
public import Theorems.Thm_SimpleGraph_RamseyBound_exists_isNClique_subset

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {n m r s : ℕ}
namespace SimpleGraph
namespace RamseyBound
theorem _root_.solution (h : RamseyBound n r s) (hnm : n ≤ m) : RamseyBound m r s := fun G => by
  rcases h.exists_isNClique_subset G (X := univ) (by simpa using hnm) with
    ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  exacts [.inl ⟨t, ht⟩, .inr ⟨t, ht⟩]
end RamseyBound
end SimpleGraph
