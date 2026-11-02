-- Prove2me | solution 1 for WilliamsonShmoys.edgeFinset_card_le_of_le__p2m_986cca2a_af96_41ca_97f1_9fc97c42977c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:22:53.957189+00:00
-- url     : https://prove2.me/submissions/0d757096-5c9c-4987-92dc-d189d3f598a1

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (K H : SimpleGraph V)
    [DecidableRel K.Adj] [DecidableRel H.Adj]
    (hKH : K ≤ H) :
    Nat.le K.edgeFinset.card H.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hKH)