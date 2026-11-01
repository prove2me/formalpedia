-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulating_extension_lower_bound__p2m_b5935805_1780_4fdc_8b62_9214cd276435_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:19:32.886193+00:00
-- url     : https://prove2.me/submissions/46b185cd-ac8d-4fbf-9d95-3d978bc38dfa
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_extension_exists__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_lower_bound__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hcard : 3 <= Fintype.card V) :
    (letI : DecidableRel G.Adj := Classical.decRel G.Adj;
      exists N : SimpleGraph V,
        G <= N /\ HasPlanarDrawingOn N /\
          (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
            3 * Fintype.card V <= N.edgeFinset.card + 6)) := by
  obtain ⟨N, hGN, hN, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_extension_exists__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
      G hG hcard
  refine ⟨N, hGN, hN, ?_⟩
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  exact WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_ed0fa66f_dbcb_4794_9398_c71658f4fffe_a1
    N hN hcard hmax
