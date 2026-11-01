-- Prove2me | solution 1 for WilliamsonShmoys.connected_of_edgeFinset_subset__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a1__p2m_074f37c1_44b5_4e2a_beb4_02cefa9615fb_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:37:49.001616+00:00
-- url     : https://prove2.me/submissions/401798af-5a39-47ff-8389-b551b02229d6

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H K : SimpleGraph V) :
    letI : ∀ G : SimpleGraph V, DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
    H.edgeFinset ⊆ K.edgeFinset → H.Connected → K.Connected := by
  classical
  intro hEdges hH
  letI : Fintype H.edgeSet := H.fintypeEdgeSet
  letI : Fintype K.edgeSet := K.fintypeEdgeSet
  exact SimpleGraph.Connected.mono
    (SimpleGraph.edgeFinset_subset_edgeFinset.mp hEdges) hH