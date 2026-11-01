-- Prove2me | solution 1 for WilliamsonShmoys.exists_edge_supergraph_of_maximum_edge_cardinality__p2m_39b66288_b9dd_430f_8b7b_434cfc203be4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:53:04.937198+00:00
-- url     : https://prove2.me/submissions/4e20bfa0-fb84-415e-98b9-abc8d4cc2284

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (dK : DecidableRel K.Adj)
    (P : SimpleGraph V → Prop)
    (hP : P K) :
    ∃ (H : SimpleGraph V) (dH : DecidableRel H.Adj),
      (letI : DecidableRel K.Adj := dK
       letI : DecidableRel H.Adj := dH
       K.edgeFinset ⊆ H.edgeFinset) ∧
      P H ∧
      ∀ (G : SimpleGraph V) (dG : DecidableRel G.Adj),
        P G →
        (letI : DecidableRel K.Adj := dK
         letI : DecidableRel G.Adj := dG
         K.edgeFinset ⊆ G.edgeFinset) →
        (letI : DecidableRel G.Adj := dG
         letI : DecidableRel H.Adj := dH
         G.edgeFinset.card ≤ H.edgeFinset.card) := by
  classical
  let s : Finset (SimpleGraph V) :=
    Finset.univ.filter fun G => K ≤ G ∧ P G
  have hs : s.Nonempty := by
    refine ⟨K, ?_⟩
    simp [s, hP]
  obtain ⟨H, hHs, hmax⟩ :=
    Finset.exists_max_image s (fun G => G.edgeFinset.card) hs
  refine ⟨H, Classical.decRel H.Adj, ?_, ?_, ?_⟩
  · letI : DecidableRel K.Adj := dK
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    exact (edgeFinset_subset_edgeFinset).2 (Finset.mem_filter.mp hHs |>.2.1)
  · exact (Finset.mem_filter.mp hHs).2.2
  · intro G dG hPG hKG
    letI : DecidableRel K.Adj := dK
    letI : DecidableRel G.Adj := dG
    letI : DecidableRel H.Adj := Classical.decRel H.Adj
    have hGs : G ∈ s := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ G, ?_⟩
      exact ⟨(edgeFinset_subset_edgeFinset).1 hKG, hPG⟩
    have hGcard :
        (letI : DecidableRel G.Adj := dG; G.edgeFinset) =
          (letI : DecidableRel G.Adj := Classical.decRel G.Adj; G.edgeFinset) := by
      ext e
      simp [SimpleGraph.edgeFinset]
    simpa only [hGcard] using hmax G hGs
