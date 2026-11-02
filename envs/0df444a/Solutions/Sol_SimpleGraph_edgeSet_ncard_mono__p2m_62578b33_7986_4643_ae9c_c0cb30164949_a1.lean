-- Prove2me | solution 1 for SimpleGraph.edgeSet_ncard_mono__p2m_62578b33_7986_4643_ae9c_c0cb30164949_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:19:35.679449+00:00
-- url     : https://prove2.me/submissions/051f69c9-0783-42c7-89fb-0966675bd996

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  classical
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono h)