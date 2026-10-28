-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_triangulation_extension_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:17:56.053059+00:00
-- url     : https://prove2.me/submissions/7d576f9b-9109-4840-8004-abb7508112b0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edgeMaximal_extension_5fac830d_330a_4033_b92d_b2d1f0f7b487
import Theorems.Thm_WilliamsonShmoys_edgeMaximal_planar_edge_count_5fac830d_330a_4033_b92d_b2d1f0f7b487

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ M : SimpleGraph V,
      N ≤ M ∧
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      N.edgeSet.ncard ≤ M.edgeSet.ncard ∧
      M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨M, hNM, hM, hMmax, hCard⟩ :=
    WilliamsonShmoys.planar_drawingOn_edgeMaximal_extension_5fac830d_330a_4033_b92d_b2d1f0f7b487 N hV hN
  have hEq := WilliamsonShmoys.edgeMaximal_planar_edge_count_5fac830d_330a_4033_b92d_b2d1f0f7b487 M hV hM hMmax
  exact ⟨M, hNM, hM, hCard, hEq⟩