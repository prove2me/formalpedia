-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_lt_of_le_of_new_edge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:10:35.484106+00:00
-- url     : https://prove2.me/submissions/5e51963d-d7e3-4f2f-b4bb-270cec92f880

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (u v : V)
    (hnot : ¬ G.Adj u v)
    (hadj : H.Adj u v) :
    G.edgeSet.ncard < H.edgeSet.ncard := by
  classical
  have hsub : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hGH
  have hss : G.edgeSet ⊂ H.edgeSet := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨hsub, ?_⟩
    intro heq
    apply hnot
    have hmemH : s(u, v) ∈ H.edgeSet :=
      H.mem_edgeSet.2 hadj
    have hmemG : s(u, v) ∈ G.edgeSet := by
      rw [heq]
      exact hmemH
    exact G.mem_edgeSet.1 hmemG
  exact Set.ncard_lt_ncard hss