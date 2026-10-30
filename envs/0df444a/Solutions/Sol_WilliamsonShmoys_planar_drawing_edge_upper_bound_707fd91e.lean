-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound_707fd91e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T18:20:53.445001+00:00
-- url     : https://prove2.me/submissions/87cb75e9-ab0d-4b4e-8f80-e336e88fad4d

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_ba8b1886_1f4e_4f59_8448_b70c4d0c6621

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    K.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨H, hKH, hH⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_ba8b1886_1f4e_4f59_8448_b70c4d0c6621 K hV hK
  have hcard : K.edgeSet.ncard <= H.edgeSet.ncard :=
    Set.ncard_mono hKH
  omega