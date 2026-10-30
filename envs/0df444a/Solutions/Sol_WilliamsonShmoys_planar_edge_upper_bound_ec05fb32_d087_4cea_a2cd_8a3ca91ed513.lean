-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_upper_bound_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T10:00:17.091393+00:00
-- url     : https://prove2.me/submissions/14a61892-50f8-427e-b454-6465c755b53d

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension_ec05fb32_d087_4cea_a2cd_8a3ca91ed513

set_option autoImplicit false

 theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    N.edgeSet.ncard + 6 <= 3 * Fintype.card V := by
  obtain ⟨M, _hNM, _hMplanar, hle, hMcount⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension_ec05fb32_d087_4cea_a2cd_8a3ca91ed513
      N hV hN
  omega