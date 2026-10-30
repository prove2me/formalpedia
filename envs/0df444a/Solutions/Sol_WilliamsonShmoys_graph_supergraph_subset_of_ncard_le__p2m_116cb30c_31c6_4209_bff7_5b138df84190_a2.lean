-- Prove2me | solution 1 for WilliamsonShmoys.graph_supergraph_subset_of_ncard_le__p2m_116cb30c_31c6_4209_bff7_5b138df84190_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:26:01.023352+00:00
-- url     : https://prove2.me/submissions/01e0abb4-5419-49de-8680-51cdebc1191d

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G.edgeSet ⊆ H.edgeSet)
    (hcard : H.edgeSet.ncard ≤ G.edgeSet.ncard) :
    H.edgeSet ⊆ G.edgeSet := by
  classical
  by_contra hnot
  have hstrict : G.edgeSet ⊂ H.edgeSet :=
    Set.ssubset_iff_subset_ne.mpr ⟨hGH, fun heq => hnot (by simpa [heq])⟩
  have hlt : G.edgeSet.ncard < H.edgeSet.ncard :=
    Set.ncard_lt_ncard hstrict
  omega