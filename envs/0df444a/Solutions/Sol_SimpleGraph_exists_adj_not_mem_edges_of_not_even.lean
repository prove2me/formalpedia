-- Prove2me | solution 1 for SimpleGraph.exists_adj_not_mem_edges_of_not_even
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T17:34:55.455086+00:00
-- url     : https://prove2.me/submissions/cb7eb9ef-925f-4788-8ae3-6b33a80e1e5d

module
public import Mathlib.Combinatorics.SimpleGraph.Trails
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Definitions.Def_Euler_Basic

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open Walk
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]
namespace SimpleGraph
theorem _root_.solution {u v x : V} {p : G.Walk u v} (hp : p.IsTrail)
    (hx : Even (G.degree x)) (hodd : ¬ Even (p.edges.countP fun e => x ∈ e)) :
    ∃ y, G.Adj x y ∧ s(x, y) ∉ p.edges := by
  by_contra! h
  apply hodd
  have hinc : G.incidenceFinset x = hp.edgesFinset.filter (x ∈ ·) := by
    ext e
    simp only [mem_incidenceFinset, incidenceSet, Set.mem_ofPred_eq, Finset.mem_filter,
      Finset.mem_mk, Multiset.mem_coe]
    constructor
    · rintro ⟨he, hxe⟩
      obtain ⟨y, rfl⟩ := Sym2.mem_iff_exists.mp hxe
      exact ⟨h y he, hxe⟩
    · rintro ⟨hm, hxe⟩
      exact ⟨p.edges_subset_edgeSet hm, hxe⟩
  have hcard : p.edges.countP (fun e => x ∈ e) = G.degree x := by
    rw [← card_incidenceFinset_eq_degree, hinc, ← Multiset.coe_countP,
      Multiset.countP_eq_card_filter]
    rfl
  rwa [hcard]
end SimpleGraph
