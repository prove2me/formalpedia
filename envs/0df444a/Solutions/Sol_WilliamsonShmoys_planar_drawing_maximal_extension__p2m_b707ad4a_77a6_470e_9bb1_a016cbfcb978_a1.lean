-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_b707ad4a_77a6_470e_9bb1_a016cbfcb978_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:59:19.981139+00:00
-- url     : https://prove2.me/submissions/937efccd-337e-43f6-976b-2857e6c5951e

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G) :
    ∃ K : SimpleGraph V, G.edgeSet ⊆ K.edgeSet ∧ HasPlanarDrawingOn K ∧
      ∀ L : SimpleGraph V, K.edgeSet ⊆ L.edgeSet → HasPlanarDrawingOn L →
        L.edgeSet = K.edgeSet := by
  classical
  let P : Finset (Sym2 V) → Prop := fun s =>
    G.edgeSet ⊆ (s : Set (Sym2 V)) ∧
      (∀ e ∈ s, ¬e.IsDiag) ∧
      HasPlanarDrawingOn (SimpleGraph.fromEdgeSet (s : Set (Sym2 V)))
  let S : Finset (Finset (Sym2 V)) := Finset.univ.filter P
  have hGmem : G.edgeFinset ∈ S := by
    simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, P]
    change G.edgeSet ⊆ (G.edgeFinset : Set (Sym2 V)) ∧
      (∀ e ∈ G.edgeFinset, ¬e.IsDiag) ∧
      HasPlanarDrawingOn (SimpleGraph.fromEdgeSet (G.edgeFinset : Set (Sym2 V)))
    constructor
    · intro e he
      change e ∈ G.edgeFinset
      simpa only [SimpleGraph.mem_edgeFinset] using he
    constructor
    · intro e he
      exact SimpleGraph.not_isDiag_of_mem_edgeFinset he
    · simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] using hG
  have hS : S.Nonempty := ⟨G.edgeFinset, hGmem⟩
  obtain ⟨s, hs, hsmax⟩ := Finset.exists_max_image S Finset.card hS
  have hsP : G.edgeSet ⊆ (s : Set (Sym2 V)) ∧
      (∀ e ∈ s, ¬e.IsDiag) ∧
      HasPlanarDrawingOn (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))) := by
    exact (Finset.mem_filter.mp hs).2
  let K : SimpleGraph V := SimpleGraph.fromEdgeSet (s : Set (Sym2 V))
  have hKedge : K.edgeSet = (s : Set (Sym2 V)) := by
    change (SimpleGraph.fromEdgeSet (s : Set (Sym2 V))).edgeSet = _
    rw [SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    simp only [Set.mem_diff, Finset.mem_coe]
    constructor
    · exact fun h => h.1
    · intro he
      exact ⟨he, by simpa using hsP.2.1 e he⟩
  have hKdraw : HasPlanarDrawingOn K := hsP.2.2
  refine ⟨K, ?_, hKdraw, ?_⟩
  · rw [hKedge]
    exact hsP.1
  · intro L hKL hLdraw
    have hLmem : L.edgeFinset ∈ S := by
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, P]
      change G.edgeSet ⊆ (L.edgeFinset : Set (Sym2 V)) ∧
        (∀ e ∈ L.edgeFinset, ¬e.IsDiag) ∧
        HasPlanarDrawingOn
          (SimpleGraph.fromEdgeSet (L.edgeFinset : Set (Sym2 V)))
      constructor
      · have hGK : G.edgeSet ⊆ K.edgeSet := by
          rw [hKedge]
          exact hsP.1
        simpa only [SimpleGraph.coe_edgeFinset] using hGK.trans hKL
      constructor
      · intro e he
        exact SimpleGraph.not_isDiag_of_mem_edgeFinset he
      · simpa only [SimpleGraph.coe_edgeFinset, SimpleGraph.fromEdgeSet_edgeSet] using hLdraw
    have hst : s ⊆ L.edgeFinset := by
      intro e he
      have heK : e ∈ K.edgeSet := by
        rw [hKedge]
        exact he
      exact (SimpleGraph.mem_edgeFinset).2 (hKL heK)
    have hcard : L.edgeFinset.card ≤ s.card := hsmax L.edgeFinset hLmem
    have heq : s = L.edgeFinset := Finset.eq_of_subset_of_card_le hst hcard
    rw [hKedge, heq, SimpleGraph.coe_edgeFinset]
