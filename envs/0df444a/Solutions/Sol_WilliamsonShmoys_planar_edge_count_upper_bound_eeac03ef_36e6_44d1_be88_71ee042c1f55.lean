-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T04:42:33.192+00:00
-- url     : https://prove2.me/submissions/084baa93-4179-4c69-b4ad-5fcae12d52f1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_maximal_face_decomposition_eeac03ef_36e6_44d1_be88_71ee042c1f55

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨M, hEdge, hSub, hDraw, hMax⟩ :=
    WilliamsonShmoys.planar_edge_count_maximal_extension_eeac03ef_36e6_44d1_be88_71ee042c1f55 L hV hL
  obtain ⟨f, hEuler, hInc⟩ :=
    WilliamsonShmoys.planar_edge_count_maximal_face_decomposition_eeac03ef_36e6_44d1_be88_71ee042c1f55
      M hV hDraw hMax
  have hMbound : M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
    omega
  exact le_trans hEdge hMbound