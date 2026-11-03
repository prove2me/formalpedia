-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_lower_bound__p2m_b9f43026_a41c_414f_8846_4d67a85cd361_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T17:16:02.655514+00:00
-- url     : https://prove2.me/submissions/c09a3b17-61dc-4896-998e-9c0a1f3fa54d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension_edge_count__p2m_cde24fc9_3673_41c5_8e3d_d0ea96c1aeba_a1
import Mathlib
open WilliamsonShmoys
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMaximal : forall K : SimpleGraph V, H <= K -> WilliamsonShmoys.HasPlanarDrawingOn K -> K = H)
    (hCard : 3 <= Fintype.card V) :
    3 * Fintype.card V - 6 <= H.edgeSet.ncard := by
  obtain ⟨K, hHK, hKDrawing, hKCount⟩ :=
    WilliamsonShmoys.maximal_planar_extension_edge_count__p2m_cde24fc9_3673_41c5_8e3d_d0ea96c1aeba_a1
      H hH hCard
  have hKH : K = H := hMaximal K hHK hKDrawing
  have hLower : 3 * Fintype.card V - 6 ≤ K.edgeSet.ncard := le_of_eq hKCount
  simpa [hKH] using hLower