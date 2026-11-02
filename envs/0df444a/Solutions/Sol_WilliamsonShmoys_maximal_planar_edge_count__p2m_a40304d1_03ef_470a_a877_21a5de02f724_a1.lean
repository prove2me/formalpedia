-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_a40304d1_03ef_470a_a877_21a5de02f724_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:59:39.351831+00:00
-- url     : https://prove2.me/submissions/1b9a3fbc-ad1e-4915-8bf7-048e52e72ebe
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2

open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hH : HasPlanarDrawingOn H)
    (hcard : 3 <= Fintype.card V)
    (hmax : forall K : SimpleGraph V,
      (forall u v, H.Adj u v -> K.Adj u v) ->
      HasPlanarDrawingOn K ->
      forall u v, K.Adj u v -> H.Adj u v) :
    H.edgeFinset.card + 6 = 3 * Fintype.card V := by
  have hUpper :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
      H hH hcard
  have hLower :=
    WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_2629fd8d_6fc9_4c07_8b09_9c33cf4a1063_a2
      H hH hcard hmax
  omega