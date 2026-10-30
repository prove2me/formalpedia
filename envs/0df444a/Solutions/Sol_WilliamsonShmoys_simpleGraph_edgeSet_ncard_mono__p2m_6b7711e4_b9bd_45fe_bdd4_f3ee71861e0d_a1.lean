-- Prove2me | solution 1 for WilliamsonShmoys.simpleGraph_edgeSet_ncard_mono__p2m_6b7711e4_b9bd_45fe_bdd4_f3ee71861e0d_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:53:37.069992+00:00
-- url     : https://prove2.me/submissions/542bac04-b51d-4ff8-a49d-c168dcbe07f9

import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G K : SimpleGraph V) (hGK : G ≤ K) :
    G.edgeSet.ncard ≤ K.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hGK)