-- Prove2me | solution 1 for SimpleGraph.exists_adj_not_mem_of_countP_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:49:38.564041+00:00
-- url     : https://prove2.me/submissions/68551eab-85a2-4304-9d01-6d857741acfd

module
public import Definitions.Def_Euler_Basic
public import Definitions.Def_Euler_Trail
public import Theorems.Thm_SimpleGraph_countP_eq_degree_of_forall_adj_mem

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {L : List (Sym2 V)} (hL : L.Nodup)
    (hsub : ∀ e ∈ L, e ∈ G.edgeSet) {x : V} (h : L.countP (fun e => x ∈ e) ≠ G.degree x) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ L := by
  by_contra! h'
  exact h (countP_eq_degree_of_forall_adj_mem hL hsub h')
end SimpleGraph
