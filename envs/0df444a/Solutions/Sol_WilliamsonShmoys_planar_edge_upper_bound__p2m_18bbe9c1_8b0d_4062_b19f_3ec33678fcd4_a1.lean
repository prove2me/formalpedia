-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound__p2m_18bbe9c1_8b0d_4062_b19f_3ec33678fcd4_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:59:27.370883+00:00
-- url     : https://prove2.me/submissions/b06c018d-4661-4d25-9f15-45e7dded2f1a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_augmentation__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdrawing : HasPlanarDrawingOn G) :
    letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
    G.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  letI : forall K : SimpleGraph V, DecidableRel K.Adj := fun K => Classical.decRel K.Adj
  obtain ⟨H, hGH, hHdrawing, hmax, hGcard⟩ :=
    WilliamsonShmoys.planar_drawing_augmentation__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
      G hcard hdrawing
  have hHcard :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_1c06af72_8ad5_473e_9376_40ba591256d7_a2
      H hcard hHdrawing hmax
  exact hGcard.trans hHcard.le