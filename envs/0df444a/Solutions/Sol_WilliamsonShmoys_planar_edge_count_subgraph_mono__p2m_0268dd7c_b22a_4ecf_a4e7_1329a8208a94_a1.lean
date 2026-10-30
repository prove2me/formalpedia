-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_subgraph_mono__p2m_0268dd7c_b22a_4ecf_a4e7_1329a8208a94_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T21:30:26.199067+00:00
-- url     : https://prove2.me/submissions/a3f0cc70-4f12-4542-9cdd-49d8b8c5b44a

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hH : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  have hcard : G.edgeSet.ncard ≤ H.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hGH)
  omega