-- Prove2me | solution 1 for SimpleGraph.RamseyBound.not_cliqueFree_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:27:57.933198+00:00
-- url     : https://prove2.me/submissions/46afb138-d1cd-4097-9e70-d19b51a98edb

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
theorem _root_.solution [Fintype V] (h : RamseyBound n r s) (G : SimpleGraph V)
    (hV : n ≤ Fintype.card V) : ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s := by
  rcases h.exists_isNClique_subset G (X := univ) (by simpa using hV) with ⟨t, -, ht⟩ | ⟨t, -, ht⟩
  exacts [.inl ht.not_cliqueFree, .inr ht.not_cliqueFree]
end RamseyBound
end SimpleGraph
