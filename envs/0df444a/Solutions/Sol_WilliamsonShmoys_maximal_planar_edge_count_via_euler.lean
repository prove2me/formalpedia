-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_via_euler
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T20:53:02.747837+00:00
-- url     : https://prove2.me/submissions/26664345-7eeb-4673-ac8c-362907f2f27a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler_planar_edge_upper_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_via_euler_maximal_lower_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (S : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hSdraw : WilliamsonShmoys.HasPlanarDrawingOn S)
    (hSmax : ∀ T : SimpleGraph V,
      S ≤ T → WilliamsonShmoys.HasPlanarDrawingOn T → T = S) :
    S.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hupper := WilliamsonShmoys.maximal_planar_edge_count_via_euler_planar_edge_upper_bound
    S hV hSdraw
  have hlower := WilliamsonShmoys.maximal_planar_edge_count_via_euler_maximal_lower_bound
    S hV hSdraw hSmax
  omega