-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_lower_bound_71955334_b5e9_40f2_bf30_231a1d4336f4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:42:23.880449+00:00
-- url     : https://prove2.me/submissions/a8d5c0d4-700d-40c2-8486-01a91ff7d105

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension_3fe8be02_4541_4d0a_bbf4_850e46d722fe

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hmax : ∀ Y : SimpleGraph V, X ≤ Y →
      WilliamsonShmoys.HasPlanarDrawingOn Y → Y = X) :
    3 * Fintype.card V ≤ X.edgeSet.ncard + 6 := by
  obtain ⟨Y, hXY, hY, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_extension_3fe8be02_4541_4d0a_bbf4_850e46d722fe X hV hX
  have hYX : Y = X := hmax Y hXY hY
  rw [hYX] at hcount
  omega