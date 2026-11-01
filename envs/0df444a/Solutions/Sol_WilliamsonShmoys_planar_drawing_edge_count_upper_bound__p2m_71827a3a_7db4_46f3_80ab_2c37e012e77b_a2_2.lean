-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_71827a3a_7db4_46f3_80ab_2c37e012e77b_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:48:35.279262+00:00
-- url     : https://prove2.me/submissions/5f69c573-e7c0-4b32-90fe-50eaafe5ee01
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_augmentation_with_three_vertices__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a2
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_edge_count_bound__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    M.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hHplanar, hHconn, hmono⟩ :=
    WilliamsonShmoys.planar_drawing_connected_augmentation_with_three_vertices__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a2
      M hplanar hcard
  have hbound :=
    WilliamsonShmoys.connected_planar_drawing_edge_count_bound__p2m_257de7f1_d94a_4116_b7e0_524ede699478_a1
      H hHplanar hHconn hcard
  omega