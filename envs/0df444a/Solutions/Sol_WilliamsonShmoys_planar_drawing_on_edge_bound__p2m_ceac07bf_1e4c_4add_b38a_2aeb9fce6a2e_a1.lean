-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_on_edge_bound__p2m_ceac07bf_1e4c_4add_b38a_2aeb9fce6a2e_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:45:52.162128+00:00
-- url     : https://prove2.me/submissions/e50b19d6-80d8-4f66-b56f-43cd24fd2332
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_edge_bound_ge_three__p2m_93958b12_2978_49ef_a2e2_395a87349bb0_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
     3 * Fintype.card V <= N.edgeFinset.card + 6) := by
  classical
  by_cases hn : 3 ≤ Fintype.card V
  · exact WilliamsonShmoys.planar_drawing_on_edge_bound_ge_three__p2m_93958b12_2978_49ef_a2e2_395a87349bb0_a1 N hN hn
  · have hcard : Fintype.card V ≤ 2 := by omega
    omega