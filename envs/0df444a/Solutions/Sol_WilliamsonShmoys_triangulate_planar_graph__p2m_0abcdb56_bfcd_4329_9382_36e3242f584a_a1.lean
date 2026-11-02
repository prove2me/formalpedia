-- Prove2me | solution 1 for WilliamsonShmoys.triangulate_planar_graph__p2m_0abcdb56_bfcd_4329_9382_36e3242f584a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:35:09.828284+00:00
-- url     : https://prove2.me/submissions/c6d4b587-d25f-4b4b-a618-2ac3f911a40e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension__p2m_71345845_0812_4936_9e60_f9671145c018_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_71345845_0812_4936_9e60_f9671145c018_a2

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : HasPlanarDrawingOn L) :
    ∃ T : SimpleGraph V, L ≤ T ∧ HasPlanarDrawingOn T ∧
      (letI : DecidableRel T.Adj := Classical.decRel T.Adj;
       3 * Fintype.card V = T.edgeFinset.card + 6) := by
  classical
  obtain ⟨T, hLT, hT, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension__p2m_71345845_0812_4936_9e60_f9671145c018_a2
      L hL
  refine ⟨T, hLT, hT, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_71345845_0812_4936_9e60_f9671145c018_a2
    T hV hT hmax