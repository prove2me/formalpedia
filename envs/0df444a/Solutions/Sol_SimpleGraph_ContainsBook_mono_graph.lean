-- Prove2me | solution 1 for SimpleGraph.ContainsBook.mono_graph
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T19:34:45.357636+00:00
-- url     : https://prove2.me/submissions/2199c743-6d20-4599-b930-39042f1ab689

module
public import Definitions.Def_RamseyReservoir_Bireservoir
public import Mathlib.Algebra.Order.Chebyshev
public import Mathlib.Combinatorics.SimpleGraph.DegreeSum
public import Definitions.Def_RamseyReservoir_Book
public import Theorems.Thm_SimpleGraph_ContainsBook_mono
public import Theorems.Thm_SimpleGraph_RamseyBound_mono


set_option autoImplicit true
@[expose] public section
public section
open Finset
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}
namespace SimpleGraph
namespace ContainsBook
theorem _root_.solution {H : SimpleGraph V} {m t : ℕ} (h : G.ContainsBook m t)
    (hGH : G ≤ H) : H.ContainsBook m t :=
  let ⟨R, hm, hp⟩ := h
  ⟨⟨R.spine, R.pool, R.isClique_spine.mono hGH, R.disjoint, fun x hx y hy => hGH (R.adj x hx y hy)⟩,
    hm, hp⟩
end ContainsBook
end SimpleGraph
