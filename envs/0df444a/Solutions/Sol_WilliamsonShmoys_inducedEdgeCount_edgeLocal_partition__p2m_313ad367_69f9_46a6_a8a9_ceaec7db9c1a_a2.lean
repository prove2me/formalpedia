-- Prove2me | solution 1 for WilliamsonShmoys.inducedEdgeCount_edgeLocal_partition__p2m_313ad367_69f9_46a6_a8a9_ceaec7db9c1a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T02:32:31.53765+00:00
-- url     : https://prove2.me/submissions/0b4f92ac-cab8-4ba8-a113-af94e1777b0b

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

set_option autoImplicit false
open scoped BigOperators

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (C : Finset (Finset V))
    (hcover : ∀ v : V, ∃ s ∈ C, v ∈ s)
    (hdisjoint : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hedgeLocal : ∀ u v : V, L.Adj u v → ∃ s ∈ C, u ∈ s ∧ v ∈ s) :
    letI : DecidableRel L.Adj := dL
    (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) = L.edgeFinset.card := by
  classical
  letI : DecidableRel L.Adj := dL
  let edgePart : Finset V → Finset (Sym2 V) :=
    fun s => L.edgeFinset.filter (fun e => e.toFinset ⊆ s)

  have hcard (s : Finset V) :
      (L.induce (↑s : Set V)).edgeFinset.card = (edgePart s).card := by
    change (L.induce (↑s : Set V)).edgeFinset.card =
      ({e ∈ L.edgeFinset | e.toFinset ⊆ s} : Finset (Sym2 V)).card
    exact (SimpleGraph.card_filter_edgeFinset_toFinset_subset (G := L) s).symm

  have hpairwise : (C : Set (Finset V)).PairwiseDisjoint edgePart := by
    intro s hs t ht hst
    apply Finset.disjoint_left.mpr
    intro e heS heT
    have hsubsetS : e.toFinset ⊆ s := (Finset.mem_filter.mp heS).2
    have hsubsetT : e.toFinset ⊆ t := (Finset.mem_filter.mp heT).2
    have hv : e.out.1 ∈ e.toFinset :=
      Sym2.mem_toFinset.mpr (Sym2.out_fst_mem e)
    have hstDisjoint := hdisjoint s hs t ht hst
    exact (Finset.disjoint_left.mp hstDisjoint) (hsubsetS hv) (hsubsetT hv)

  have hunion : C.biUnion edgePart = L.edgeFinset := by
    ext e
    refine e.inductionOn ?_
    intro u v
    constructor
    · intro he
      rcases Finset.mem_biUnion.mp he with ⟨s, hs, hmem⟩
      exact (Finset.mem_filter.mp hmem).1
    · intro he
      have hadj : L.Adj u v := by
        simpa only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet] using he
      obtain ⟨s, hs, hus, hvs⟩ := hedgeLocal u v hadj
      have hsub : (Sym2.mk u v).toFinset ⊆ s := by
        intro x hx
        rw [Sym2.toFinset_mk_eq, Finset.mem_insert, Finset.mem_singleton] at hx
        rcases hx with rfl | rfl
        · exact hus
        · exact hvs
      have hmem : Sym2.mk u v ∈ edgePart s :=
        Finset.mem_filter.mpr ⟨he, hsub⟩
      exact Finset.mem_biUnion.mpr ⟨s, hs, hmem⟩

  calc
    (∑ s ∈ C, (L.induce (↑s : Set V)).edgeFinset.card) =
        ∑ s ∈ C, (edgePart s).card := by
          apply Finset.sum_congr rfl
          intro s hs
          exact hcard s
    _ = (C.biUnion edgePart).card := (Finset.card_biUnion hpairwise).symm
    _ = L.edgeFinset.card := congrArg Finset.card hunion
