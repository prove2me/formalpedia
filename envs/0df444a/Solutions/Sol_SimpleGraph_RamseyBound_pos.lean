-- Prove2me | solution 1 for SimpleGraph.RamseyBound.pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:27.313851+00:00
-- url     : https://prove2.me/submissions/c39bbca4-f7a8-4a4f-9a20-f6ec07660370

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
namespace RamseyBound
theorem _root_.solution (h : RamseyBound n r s) (hr : 0 < r) (hs : 0 < s) : 0 < n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · rcases h ⊥ with ⟨t, ht⟩ | ⟨t, ht⟩ <;>
    · have := ht.card_eq
      rw [Subsingleton.elim t ∅, card_empty] at this
      omega
  · exact hn
end RamseyBound
end SimpleGraph
