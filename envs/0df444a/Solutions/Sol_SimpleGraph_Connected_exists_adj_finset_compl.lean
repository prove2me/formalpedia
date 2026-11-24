-- Prove2me | solution 1 for SimpleGraph.Connected.exists_adj_finset_compl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:26:03.995849+00:00
-- url     : https://prove2.me/submissions/c2b09d7f-31a8-41d8-834e-1f28372158d3

module
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.Girth
public import Mathlib.Data.Set.Finite.Lemmas
public import Definitions.Def_Wowii84_LargestInducedTree

set_option autoImplicit false
@[expose] public section
public section
open SimpleGraph
variable {α : Type*} [Fintype α] [DecidableEq α]
namespace SimpleGraph
namespace Connected
theorem _root_.solution {G : SimpleGraph α}
    (hG : G.Connected) {s : Finset α} (hs : s.Nonempty) (hsu : s ≠ Finset.univ) :
    ∃ z ∉ s, ∃ a ∈ s, G.Adj z a := by
  obtain ⟨u, hu⟩ := hs
  have hzex : ∃ z : α, z ∉ s := by
    by_contra hn
    push Not at hn
    apply hsu
    exact Finset.eq_univ_of_forall hn
  obtain ⟨z, hz⟩ := hzex
  obtain ⟨p⟩ := hG u z
  obtain ⟨d, _, hd_in, hd_out⟩ :=
    p.exists_boundary_dart (s : Set α) (by simpa) (by simpa)
  exact ⟨d.snd, by simpa using hd_out, d.fst, by simpa using hd_in, d.adj.symm⟩
end Connected
end SimpleGraph
