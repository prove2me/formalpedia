-- Prove2me | solution 1 for SimpleGraph.ContainsBook.not_cliqueFree_or
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:06.560224+00:00
-- url     : https://prove2.me/submissions/0f53a6e8-34ae-442d-93f1-865299e9ad78

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_Reservoir_exists_of_ramseyBound
public import Theorems.Thm_SimpleGraph_Bireservoir_exists_of_ramseyBound


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace SimpleGraph
namespace ContainsBook
theorem _root_.solution {m n r s : ℕ} (hB : G.ContainsBook m n)
    (h : RamseyBound n (r - m) s) : ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s := by
  obtain ⟨R, rfl, hn⟩ := hB
  rcases R.exists_of_ramseyBound h hn with ⟨t, ht⟩ | ⟨t, ht⟩
  exacts [.inl ht.not_cliqueFree, .inr ht.not_cliqueFree]
end ContainsBook
end SimpleGraph
