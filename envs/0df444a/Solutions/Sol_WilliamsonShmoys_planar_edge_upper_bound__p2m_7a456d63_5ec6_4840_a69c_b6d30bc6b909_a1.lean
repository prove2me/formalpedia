-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_7a456d63_5ec6_4840_a69c_b6d30bc6b909_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T22:26:40.377118+00:00
-- url     : https://prove2.me/submissions/74d5bbab-d96f-47df-9611-8ed7a890fdf6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_connected_edge_upper_bound__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_completion__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

/-- The planar simple-graph edge bound obtained by connected completion and
Euler's inequality. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    (hLplanar : HasPlanarDrawingOn L) (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, _hLH, hHplanar, hHconn, hEdges⟩ :=
    WilliamsonShmoys.planar_drawing_connected_completion__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
      L hLplanar hV
  have hBound :=
    WilliamsonShmoys.planar_connected_edge_upper_bound__p2m_d61810ad_72dd_44a6_9339_c836b4de23da_a1
      H hHplanar hHconn hV
  exact hEdges.trans hBound