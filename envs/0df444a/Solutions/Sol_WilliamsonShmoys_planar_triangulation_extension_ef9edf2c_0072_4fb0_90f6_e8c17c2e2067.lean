-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T16:22:12.479744+00:00
-- url     : https://prove2.me/submissions/adc10be4-a924-4a20-a6cf-fb08bb8a9169

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067

set_option autoImplicit false

/-- Extend a drawable graph on at least three vertices to a drawable graph with the triangulated edge count. -/
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    ∃ H : SimpleGraph V,
      G ≤ H ∧ WilliamsonShmoys.HasPlanarDrawingOn H ∧
        H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067 G hG
  exact ⟨H, hGH, hH,
    WilliamsonShmoys.maximal_planar_edge_count_for_triangulation_extension_ef9edf2c_0072_4fb0_90f6_e8c17c2e2067 H hV hH hmax⟩