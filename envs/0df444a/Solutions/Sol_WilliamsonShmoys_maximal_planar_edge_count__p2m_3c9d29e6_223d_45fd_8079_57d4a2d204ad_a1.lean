-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count__p2m_3c9d29e6_223d_45fd_8079_57d4a2d204ad_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:27:54.714668+00:00
-- url     : https://prove2.me/submissions/4447dd46-06ea-45d3-867c-6e43a60643cf

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_edge_upper_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_lower_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hcard : 3 <= Fintype.card V)
    (hM : HasPlanarDrawingOn M)
    (hmax : ∀ N : SimpleGraph V, M <= N → HasPlanarDrawingOn N → N = M) :
    (letI : (G : SimpleGraph V) -> DecidableRel G.Adj :=
      fun G => Classical.decRel G.Adj
     M.edgeFinset.card = 3 * Fintype.card V - 6) := by
  have hUpper := WilliamsonShmoys.planar_edge_upper_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2 M hcard hM
  have hLower := WilliamsonShmoys.maximal_planar_edge_lower_bound__p2m_08c24848_031b_43ea_aa26_092fb49494c8_a2 M hcard hM hmax
  omega