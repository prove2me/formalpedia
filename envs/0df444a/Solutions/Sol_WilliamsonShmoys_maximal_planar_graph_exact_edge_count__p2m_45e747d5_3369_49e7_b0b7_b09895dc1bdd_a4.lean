-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_exact_edge_count__p2m_45e747d5_3369_49e7_b0b7_b09895dc1bdd_a4
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:14:17.743989+00:00
-- url     : https://prove2.me/submissions/6467b8bc-fb17-4440-974f-7a9c63070ebd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_upper_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_lower_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hmax : ∀ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) →
      WilliamsonShmoys.HasPlanarDrawingOn P →
      ∀ u v, P.Adj u v → N.Adj u v) :
    N.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hupper := WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
    N hcard hN
  have hlower := WilliamsonShmoys.maximal_drawable_edge_lower_bound__p2m_84b83a52_4380_4290_8494_df49bd55089b_a1
    N hcard hN hmax
  omega