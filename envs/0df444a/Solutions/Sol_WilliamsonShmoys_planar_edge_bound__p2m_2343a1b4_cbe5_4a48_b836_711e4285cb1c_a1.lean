-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_bound__p2m_2343a1b4_cbe5_4a48_b836_711e4285cb1c_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:32:47.50225+00:00
-- url     : https://prove2.me/submissions/adf9c482-9d88-4ef6-8ee7-9a14514d399e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected_extension__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_bound_connected__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hplanar : HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hKplanar, hKconn, hcard⟩ :=
    WilliamsonShmoys.planar_edge_bound_connected_extension__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1 H hplanar
  have hbound :=
    WilliamsonShmoys.planar_edge_bound_connected__p2m_1e99581f_fcbc_4e9a_9e15_d8d615ea77d1_a1 K hKplanar hKconn hV
  omega