-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_graph_has_euler_edge_count_eeac03ef_36e6_44d1_be88_71ee042c1f55
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:26:55.554992+00:00
-- url     : https://prove2.me/submissions/f429be57-d0da-460c-a722-06417eaa8003
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ M : SimpleGraph V, L ≤ M →
      WilliamsonShmoys.HasPlanarDrawingOn M → M ≤ L) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper :
      L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_edge_count_upper_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55 L hV hL
  have hlower :
      3 * Fintype.card V - 6 ≤ L.edgeSet.ncard :=
    WilliamsonShmoys.maximal_planar_edge_count_lower_bound_eeac03ef_36e6_44d1_be88_71ee042c1f55 L hV hL hmax
  omega