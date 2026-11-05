-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_maximality__p2m_934089cc_df1f_4da4_b973_c115b2e35af8_a5
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T16:45:13.138237+00:00
-- url     : https://prove2.me/submissions/e47b4fe7-ce37-425f-91db-5affc6a4419d

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    {G L : SimpleGraph V} [Fintype G.edgeSet] [Fintype L.edgeSet]
    (hGL : G ≤ L)
    (hcard : L.edgeFinset.card ≤ G.edgeFinset.card) :
    L = G := by
  have heq : G.edgeFinset = L.edgeFinset :=
    Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hGL) hcard
  simpa only [SimpleGraph.edgeFinset_inj] using heq.symm
