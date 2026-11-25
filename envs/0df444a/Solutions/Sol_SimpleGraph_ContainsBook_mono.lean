-- Prove2me | solution 1 for SimpleGraph.ContainsBook.mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:32:11.343806+00:00
-- url     : https://prove2.me/submissions/556798e1-944d-4263-86dd-782d33b1d1b8

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book

set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace SimpleGraph
namespace ContainsBook
theorem _root_.solution {m t t' : ℕ} (h : G.ContainsBook m t) (ht : t' ≤ t) :
    G.ContainsBook m t' :=
  let ⟨R, hm, hp⟩ := h
  ⟨R, hm, ht.trans hp⟩
end ContainsBook
end SimpleGraph
