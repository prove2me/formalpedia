-- Prove2me | solution 2 for WilliamsonShmoys.disconnected_planar_graph_has_strict_edge_deficit__p2m_79b6cb48_7614_4e86_94da_1fe8fbba64b0_a4
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:25:58.637796+00:00
-- url     : https://prove2.me/submissions/d65b3697-b274-44aa-a350-6289f4559ebd

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hdisconnected : ¬ H.Connected) :
    H.edgeSet.ncard + 6 < 3 * Fintype.card V := by
  have h := WilliamsonShmoys.disconnected_planar_edge_bound__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
    H hplanar hV hdisconnected
  omega
