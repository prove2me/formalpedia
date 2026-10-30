-- Prove2me | solution 1 for WilliamsonShmoys.subgraph_edgeSet_ncard_mono__p2m_eac4b030_cd26_487c_98af_ec9d769936c5_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T23:47:01.713929+00:00
-- url     : https://prove2.me/submissions/07e16f0d-9a06-4874-9c02-8fd55e95e178

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M H : SimpleGraph V)
    (hMH : M ≤ H) :
    M.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hMH)