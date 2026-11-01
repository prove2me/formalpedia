-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_eq_reverse_le__p2m_1bb19ac6_452e_443b_a585_944a9ce0af63_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:56:23.733593+00:00
-- url     : https://prove2.me/submissions/e9f0c9e9-1150-441e-9e35-bc1eda1d66d2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G H : SimpleGraph V)
    (hGH : G ≤ H)
    (hcard : G.edgeSet.ncard = H.edgeSet.ncard) :
    H ≤ G := by
  have hsub : G.edgeSet ⊆ H.edgeSet := SimpleGraph.edgeSet_mono hGH
  have hedge : G.edgeSet = H.edgeSet :=
    Set.eq_of_subset_of_ncard_le hsub (le_of_eq hcard.symm)
  have hgraph : G = H := SimpleGraph.edgeSet_inj.mp hedge
  exact le_of_eq hgraph.symm