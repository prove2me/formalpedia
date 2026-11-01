-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound__p2m_9518e4d8_9181_45e5_8d65_e8b1bfbc442a_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T22:03:00.074546+00:00
-- url     : https://prove2.me/submissions/4434e77c-e949-4fb9-9568-e8e83510d648

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard <= 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
      G hG
  have hcount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_f4d7c237_0776_4adb_8bad_5150d3e32462_a1
      H hcard hH hmax
  exact le_trans (Set.ncard_le_ncard hGH) hcount
