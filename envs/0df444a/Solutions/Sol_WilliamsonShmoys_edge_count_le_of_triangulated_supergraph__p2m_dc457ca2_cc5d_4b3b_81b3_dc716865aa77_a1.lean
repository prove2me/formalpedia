-- Prove2me | solution 1 for WilliamsonShmoys.edge_count_le_of_triangulated_supergraph__p2m_dc457ca2_cc5d_4b3b_81b3_dc716865aa77_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:46:21.448423+00:00
-- url     : https://prove2.me/submissions/09049477-b17a-4734-95bc-da3a2d97e6bb

import Mathlib

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G H : SimpleGraph V) (dG : DecidableRel G.Adj) (dH : DecidableRel H.Adj)
    (hsub : (letI : DecidableRel G.Adj := dG; letI : DecidableRel H.Adj := dH; G.edgeFinset ⊆ H.edgeFinset))
    (hcard : (letI : DecidableRel H.Adj := dH; H.edgeFinset.card = 3 * Fintype.card V - 6)) :
    (letI : DecidableRel G.Adj := dG; G.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  letI : DecidableRel G.Adj := dG
  letI : DecidableRel H.Adj := dH
  calc
    G.edgeFinset.card ≤ H.edgeFinset.card := Finset.card_le_card hsub
    _ = 3 * Fintype.card V - 6 := hcard