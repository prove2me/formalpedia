-- Prove2me | solution 1 for WilliamsonShmoys.strict_edge_count_of_connected_supergraph__p2m_b7cc0e50_4117_438e_97b3_add0d92d7fc9_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T20:07:16.267212+00:00
-- url     : https://prove2.me/submissions/45ffece6-1668-4d6e-8c4f-a78a643ee2e7

import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : H.Connected)
    (hG : ¬ G.Connected) :
    G.edgeSet.ncard + 1 ≤ H.edgeSet.ncard := by
  have hedge : G.edgeSet ⊂ H.edgeSet := by
    apply Set.ssubset_iff_subset_ne.mpr
    refine ⟨SimpleGraph.edgeSet_mono hGH, ?_⟩
    intro heq
    have hHG : H ≤ G :=
      SimpleGraph.edgeSet_subset_edgeSet.mp
        (by simpa [heq] using (SimpleGraph.edgeSet_mono hGH))
    exact hG (hH.mono hHG)
  have hcard : G.edgeSet.ncard < H.edgeSet.ncard :=
    Set.ncard_lt_ncard hedge
  omega
