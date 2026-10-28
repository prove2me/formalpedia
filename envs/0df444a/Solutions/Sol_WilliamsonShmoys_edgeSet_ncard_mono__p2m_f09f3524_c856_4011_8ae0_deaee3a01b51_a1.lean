-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_mono__p2m_f09f3524_c856_4011_8ae0_deaee3a01b51_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:08:30.591761+00:00
-- url     : https://prove2.me/submissions/98c66a40-74a9-4078-9ad6-e211e071ed06

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

set_option autoImplicit false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [DecidableEq V]
    (G H : SimpleGraph V) (h : G ≤ H) :
    G.edgeSet.ncard ≤ H.edgeSet.ncard := by
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono h)