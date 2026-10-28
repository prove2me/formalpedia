-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_19f31498_c1c5_41a0_a186_562a063d6dde
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T19:04:09.743969+00:00
-- url     : https://prove2.me/submissions/7f7873dc-4194-4b98-96bb-cd8c710dacfb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_triangulation_extension_20261027

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H.edgeSet ⊆ J.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn J →
      J.edgeSet = H.edgeSet) :
    H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hsub, hJ, hcount⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_triangulation_extension_20261027 H hV hH
  have hedge : J.edgeSet = H.edgeSet := hMax J hsub hJ
  rw [← hedge]
  exact hcount