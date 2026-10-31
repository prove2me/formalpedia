-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension__p2m_8874575c_8d28_40c2_984e_f8a2d2056536_a4
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:42:07.494304+00:00
-- url     : https://prove2.me/submissions/596c6be1-8319-4dbe-ab84-bdcde1bf1e51

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_graph_extension_maximal__p2m_624a938d_c9e5_41fb_88c5_28ffcc896cfe_a1

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDraw : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ T : SimpleGraph V, H ≤ T ∧ WilliamsonShmoys.HasPlanarDrawingOn T ∧
      ∀ U : SimpleGraph V, T ≤ U → WilliamsonShmoys.HasPlanarDrawingOn U → U = T := by
  exact WilliamsonShmoys.finite_graph_extension_maximal__p2m_624a938d_c9e5_41fb_88c5_28ffcc896cfe_a1
    H WilliamsonShmoys.HasPlanarDrawingOn hDraw