-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_exact_edge_count__p2m_3ea1a2df_ff39_4335_a398_1933022707b1_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:20:08.494863+00:00
-- url     : https://prove2.me/submissions/a4ceb155-c45a-4f3a-8af1-7ec87b7f0ef1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hMdraw : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hMmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hupper :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
      M hcard hMdraw
  have hlower :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower_bound__p2m_2ddf171d_07d8_49d9_9393_f959b6989517_a3
      M hcard hMdraw hMmax
  omega