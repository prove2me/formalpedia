-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_component_reduction__p2m_263e0430_0bed_4695_a55f_33a5be744a5b_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:03:09.311519+00:00
-- url     : https://prove2.me/submissions/03b8be62-b2aa-4924-b1a8-598cd4340cd9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_partition_certificate__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
import Theorems.Thm_WilliamsonShmoys_planar_drawing_component_edge_count_aggregation__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N)
    (hconnected : ∀ {W : Type} [Fintype W] [LinearOrder W]
      (G : SimpleGraph W) (hW : 3 ≤ Fintype.card W)
      (hconn : G.Connected) (hG : HasPlanarDrawingOn G),
      (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
       G.edgeFinset.card + 6 ≤ 3 * Fintype.card W)) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     N.edgeFinset.card + 6 ≤ 3 * Fintype.card V) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  obtain ⟨C, hpos, hdisj, hcover, hcard, hbig, hsingle, hpair, hedge⟩ :=
    WilliamsonShmoys.planar_drawing_component_partition_certificate__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2 N hN
  exact WilliamsonShmoys.planar_drawing_component_edge_count_aggregation__p2m_f38f8ad9_68a6_4655_b531_6345ea797061_a2
    N hV hconnected C hpos hdisj hcover hcard hbig hsingle hpair hedge