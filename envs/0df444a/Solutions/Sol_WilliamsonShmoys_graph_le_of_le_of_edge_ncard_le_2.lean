-- Prove2me | solution 2 for WilliamsonShmoys.graph_le_of_le_of_edge_ncard_le
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:41:27.442344+00:00
-- url     : https://prove2.me/submissions/0fdd154b-b2a0-4db3-b1ad-51a2b4c77a57

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) (hMN : M ≤ N)
    (hcard : N.edgeSet.ncard ≤ M.edgeSet.ncard) :
    N ≤ M := by
  classical
  have hsub : M.edgeSet ⊆ N.edgeSet := SimpleGraph.edgeSet_mono hMN
  have hfinite : N.edgeSet.Finite := Set.toFinite _
  have hedge : M.edgeSet = N.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub hcard hfinite
  apply SimpleGraph.edgeSet_subset_edgeSet.mp
  rw [hedge]
