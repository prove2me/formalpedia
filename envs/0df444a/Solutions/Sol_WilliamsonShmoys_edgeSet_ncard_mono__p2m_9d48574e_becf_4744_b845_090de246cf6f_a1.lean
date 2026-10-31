-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_9d48574e_becf_4744_b845_090de246cf6f_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T09:22:53.198391+00:00
-- url     : https://prove2.me/submissions/bf3f6821-f0fd-443c-9bde-37e861c1681e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G H : SimpleGraph V) (hGH : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_le_ncard (SimpleGraph.edgeSet_subset_edgeSet.mpr hGH)