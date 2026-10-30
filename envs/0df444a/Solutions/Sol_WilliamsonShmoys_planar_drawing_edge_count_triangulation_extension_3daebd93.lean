-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_count_triangulation_extension_3daebd93
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T21:39:48.581244+00:00
-- url     : https://prove2.me/submissions/5f4cc8cb-95f8-4da8-a736-2acc99e3d54a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_3daebd93
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_3daebd93

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_3daebd93 H hH
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.maximal_planar_drawing_edge_count_3daebd93 K hV hK hMax⟩