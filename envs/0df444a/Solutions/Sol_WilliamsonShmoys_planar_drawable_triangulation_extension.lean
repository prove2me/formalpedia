-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawable_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T17:35:02.07978+00:00
-- url     : https://prove2.me/submissions/03b43db2-158c-4193-a7da-ad176a8eb72b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawable_maximal_extension_finite
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_euler

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H ≤ K ∧ K.edgeSet.ncard + 6 = 3 * Fintype.card V ∧
        WilliamsonShmoys.HasPlanarDrawingOn K := by
  obtain ⟨K, hHK, hK, hKmax⟩ :=
    WilliamsonShmoys.planar_drawable_maximal_extension_finite H hV hH
  have hcount :=
    WilliamsonShmoys.maximal_planar_drawing_edge_count_euler K hV hK hKmax
  exact ⟨K, hHK, hcount, hK⟩