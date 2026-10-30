-- Prove2me | solution 1 for WilliamsonShmoys.sup_inserted_nonedge_has_more_edges__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a1__p2m_468912c8_f62d_4992_8d85_065aef654ab4_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:42:12.619524+00:00
-- url     : https://prove2.me/submissions/07751c34-8340-40c6-9e49-b667dd5683b0

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (G : SimpleGraph V)
    (u v : V) (huv : u < v) (hnot : ¬ G.Adj u v) :
    G.edgeSet.ncard < (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet.ncard := by
  classical
  have huvne : u ≠ v := ne_of_lt huv
  have hnotmem : s(u, v) ∉ G.edgeSet := by
    simpa [SimpleGraph.mem_edgeSet] using hnot
  have hdiag : s(u, v) ∉ Sym2.diagSet := by
    simp [Sym2.mem_diagSet, Sym2.mk_isDiag_iff, huvne]
  have hAug : (G ⊔ SimpleGraph.fromEdgeSet {s(u, v)}).edgeSet =
      insert s(u, v) G.edgeSet := by
    rw [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet]
    ext e
    by_cases he : e = s(u, v)
    · subst e
      simp [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet, hdiag]
    · simp [SimpleGraph.edgeSet_sup, SimpleGraph.edgeSet_fromEdgeSet, he]
  rw [hAug]
  apply Set.ncard_lt_ncard
  · refine ⟨Set.subset_insert _ _, ?_⟩
    intro h
    exact hnotmem (h (by simp))
  · exact Set.toFinite _