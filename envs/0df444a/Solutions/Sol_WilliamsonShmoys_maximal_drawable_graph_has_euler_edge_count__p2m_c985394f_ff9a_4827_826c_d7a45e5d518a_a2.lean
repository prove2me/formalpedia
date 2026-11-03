-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count__p2m_c985394f_ff9a_4827_826c_d7a45e5d518a_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:40:55.180375+00:00
-- url     : https://prove2.me/submissions/a0874391-b370-4e3f-a074-a5215d3165e7

import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_lower_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
import Mathlib

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 <= Fintype.card V)
    (hdraw : HasPlanarDrawingOn N)
    (hmax : forall H : SimpleGraph V,
      (forall u v, N.Adj u v -> H.Adj u v) ->
      HasPlanarDrawingOn H -> H = N) :
    letI : forall H : SimpleGraph V, DecidableRel H.Adj := fun H => Classical.decRel H.Adj
    3 * Fintype.card V - 6 = N.edgeFinset.card := by
  have hlow := WilliamsonShmoys.maximal_drawable_edge_count_lower_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
    N hcard hdraw hmax
  have hupp := WilliamsonShmoys.planar_edge_count_upper_bound__p2m_1457b1f6_ab39_4e2c_8649_eee2274adac4_a1
    N hcard hdraw
  omega
