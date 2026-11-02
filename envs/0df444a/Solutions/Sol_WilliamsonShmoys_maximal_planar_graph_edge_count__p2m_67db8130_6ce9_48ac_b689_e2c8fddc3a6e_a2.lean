-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_67db8130_6ce9_48ac_b689_e2c8fddc3a6e_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:28:39.225414+00:00
-- url     : https://prove2.me/submissions/a85a6044-367e-4ff4-945f-1f60c0f5fb61
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
import Theorems.Thm_WilliamsonShmoys_planar_simple_edge_upper_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1
import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ P : SimpleGraph V, N ≤ P → WilliamsonShmoys.HasPlanarDrawingOn P → P = N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  letI : DecidableRel N.Adj := Classical.decRel N.Adj
  have hlow := WilliamsonShmoys.planar_maximal_edge_lower_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1 N hN hcard hmax
  have hhigh := WilliamsonShmoys.planar_simple_edge_upper_bound__p2m_6582e0a3_76e8_4a07_8065_8715ca29a41a_a1 N hN hcard
  omega