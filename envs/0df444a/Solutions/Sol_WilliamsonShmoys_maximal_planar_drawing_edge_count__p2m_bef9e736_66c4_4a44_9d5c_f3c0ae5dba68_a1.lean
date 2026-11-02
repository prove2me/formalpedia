-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count__p2m_bef9e736_66c4_4a44_9d5c_f3c0ae5dba68_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:45:22.778439+00:00
-- url     : https://prove2.me/submissions/de3392a8-84e0-4a77-ab92-c9a453a9ed10
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_upper__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_lower__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, M ≤ K → HasPlanarDrawingOn K → K ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
      3 * Fintype.card V = M.edgeFinset.card + 6) := by
  classical
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  have hUpper : M.edgeFinset.card + 6 ≤ 3 * Fintype.card V :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_upper__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
      M hM hV
  have hLower : 3 * Fintype.card V ≤ M.edgeFinset.card + 6 :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_lower__p2m_1585a545_fd39_4184_a40c_5ddea241da05_a1
      M hM hV hMax
  omega