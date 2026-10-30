-- Prove2me | solution 1 for WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:31:22.521907+00:00
-- url     : https://prove2.me/submissions/f5bad227-3d70-4126-a4a2-93e65d8eda96
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLplanar : HasPlanarDrawingOn L)
    (hLconn : L.Connected)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hLH, hHplanar, hLE, hMax⟩ :=
    WilliamsonShmoys.planar_maximal_completion__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
      L hLplanar
  have hHE :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_faad2303_0a65_471d_a30c_3c1398903a00_a1
      H hHplanar hV hMax
  omega