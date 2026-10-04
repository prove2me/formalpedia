-- Prove2me | solution 1 for OPG500Counterexample.eight_vertex_graph_structure
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-07T21:29:01.499821+00:00
-- url     : https://prove2.me/submissions/c892327a-4939-4c55-bac2-b213b018951a

import Definitions.Def_opg500_eight_vertex_graph
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Powerset

open OPG500Counterexample
open SimpleGraph

namespace FinitePeripheralGraph

private def twoRegular {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (s : Finset V) : Prop :=
  ∀ v ∈ s, (s.filter (G.Adj v)).card = 2

private theorem chordless_iff_twoRegular {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {u : V} {p : G.Walk u u}
    (hp : p.IsCycle) : p.IsChordless ↔ twoRegular G p.support.toFinset := by
  have hsubset (v : V) : p.toSubgraph.neighborSet v ⊆
      (p.support.toFinset.filter (G.Adj v) : Set V) := by
    intro w hw
    change p.toSubgraph.Adj v w at hw
    exact Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr
      (p.mem_support_of_adj_toSubgraph hw.symm), p.toSubgraph.adj_sub hw⟩
  constructor
  · intro hchord v hv
    have hv' := List.mem_toFinset.mp hv
    have heq : p.toSubgraph.neighborSet v =
        (p.support.toFinset.filter (G.Adj v) : Set V) := by
      apply Set.Subset.antisymm (hsubset v)
      intro w hw
      obtain ⟨hw, hadj⟩ := Finset.mem_filter.mp hw
      exact Walk.adj_toSubgraph_iff_mem_edges.mpr
        (hchord.mem_edges hv' (List.mem_toFinset.mp hw) hadj)
    have hcard := hp.ncard_neighborSet_toSubgraph_eq_two hv'
    simpa only [heq, Set.ncard_coe_finset] using hcard
  · intro hdegree
    apply Walk.isChordless_iff_forall_mem_edges.mpr
    intro v w hv hw hadj
    have hcard : (p.support.toFinset.filter (G.Adj v) : Set V).ncard ≤
        (p.toSubgraph.neighborSet v).ncard := by
      simp only [Set.ncard_coe_finset, hdegree v (List.mem_toFinset.mpr hv),
        hp.ncard_neighborSet_toSubgraph_eq_two hv, le_refl]
    have heq := Set.eq_of_subset_of_ncard_le (hsubset v) hcard
    apply Walk.adj_toSubgraph_iff_mem_edges.mp
    have hmem : w ∈ (p.support.toFinset.filter (G.Adj v) : Set V) :=
      Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hw, hadj⟩
    rw [← heq] at hmem
    exact hmem

/-- A finite adjacency certificate for connectivity, with no walk enumeration. -/
private def twoStepHub {V : Type*} [DecidableEq V] (G : SimpleGraph V)
    (s : Finset V) : Prop :=
  ∃ c ∈ s, ∀ v ∈ s,
    v = c ∨ G.Adj v c ∨ ∃ w ∈ s, G.Adj v w ∧ G.Adj w c

private theorem connected_of_twoStepHub {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (s : Finset V) (h : twoStepHub G s) :
    (G.induce (s : Set V)).Connected := by
  obtain ⟨c, hc, hhub⟩ := h
  apply (connected_iff_exists_forall_reachable _).mpr
  refine ⟨⟨c, hc⟩, ?_⟩
  intro v
  suffices (G.induce (s : Set V)).Reachable v ⟨c, hc⟩ from this.symm
  rcases hhub v.val v.property with hvc | hvc | ⟨w, hw, hvw, hwc⟩
  · have hv : v = ⟨c, hc⟩ := Subtype.ext hvc
    subst v
    exact Reachable.rfl
  · exact (show (G.induce (s : Set V)).Adj v ⟨c, hc⟩ from hvc).reachable
  · exact (show (G.induce (s : Set V)).Adj v ⟨w, hw⟩ from hvw).reachable.trans
      (show (G.induce (s : Set V)).Adj ⟨w, hw⟩ ⟨c, hc⟩ from hwc).reachable

private instance : DecidableRel H.Adj :=
  inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet
    (eightVertexEdges : Set (Sym2 Vertex))).Adj)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem deletion_hubs (s : Finset Vertex) (hs : s.card < 3) :
    twoStepHub H (Finset.univ \ s) := by
  revert s hs
  simp only [twoStepHub]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem triple_certificates (s : Finset Vertex) (hs : s ∈ peripheralTriples) :
    twoRegular H s ∧ twoStepHub H (Finset.univ \ s) := by
  revert s hs
  simp only [twoRegular, twoStepHub]
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
private theorem degree_two_classification (s : Finset Vertex) (hs : s.Nonempty)
    (hdegree : twoRegular H s) :
    s ∈ peripheralTriples ∨
      ∃ v ∉ s, ∃ w ∉ s, v ≠ w ∧ ∀ z ∉ s, ¬ H.Adj v z := by
  revert s hs hdegree
  simp only [twoRegular]
  decide +kernel

-- Target: e22fbdd7-a649-4c23-a6c8-e342a48654b8.
theorem solution : IsThreeConnected H ∧
    ∀ C : Cycle H, C.IsPeripheral ↔ C.walk.support.toFinset ∈ peripheralTriples := by
  constructor
  · refine ⟨by decide, ?_⟩
    intro s hs
    have hconn := connected_of_twoStepHub H _ (deletion_hubs s hs)
    have heq : ((Finset.univ \ s : Finset Vertex) : Set Vertex) = {v | v ∉ s} := by
      ext v
      simp
    rw [heq] at hconn
    exact hconn
  · intro C
    constructor
    · rintro ⟨hchord, houtside⟩
      have hnonempty : C.walk.support.toFinset.Nonempty := ⟨C.base, by simp⟩
      have hdegree := (chordless_iff_twoRegular C.isCycle).mp hchord
      rcases degree_two_classification _ hnonempty hdegree with h | ⟨v, hv, w, hw, hne, hi⟩
      · exact h
      · exfalso
        have hv' : v ∉ C.vertexSet := by simpa [Cycle.vertexSet] using hv
        have hw' : w ∉ C.vertexSet := by simpa [Cycle.vertexSet] using hw
        rcases houtside with hempty | hconn
        · exact hempty.false ⟨v, hv'⟩
        · have hne' : (⟨v, hv'⟩ : {z : Vertex // z ∉ C.vertexSet}) ≠ ⟨w, hw'⟩ :=
            fun h ↦ hne (congrArg Subtype.val h)
          obtain ⟨z, hz⟩ := (hconn ⟨v, hv'⟩ ⟨w, hw'⟩).nonempty_neighborSet_left hne'
          exact hi z.val (by simpa [Cycle.vertexSet] using z.property) hz
    · intro hs
      obtain ⟨hdegree, hhub⟩ := triple_certificates _ hs
      refine ⟨(chordless_iff_twoRegular C.isCycle).mpr hdegree, Or.inr ?_⟩
      have hconn := connected_of_twoStepHub H _ hhub
      have heq : ((Finset.univ \ C.walk.support.toFinset : Finset Vertex) : Set Vertex) =
          {v | v ∉ C.vertexSet} := by
        ext v
        simp [Cycle.vertexSet]
      rw [heq] at hconn
      exact hconn

end FinitePeripheralGraph

theorem solution : IsThreeConnected H ∧
    ∀ C : Cycle H, C.IsPeripheral ↔ C.walk.support.toFinset ∈ peripheralTriples :=
  FinitePeripheralGraph.solution

#print axioms solution
