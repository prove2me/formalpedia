-- Prove2me | solution 1 for WilliamsonShmoys.edge_maximal_planar_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T19:56:34.375549+00:00
-- url     : https://prove2.me/submissions/7819eb89-6c9c-46b2-b4df-c0cb38b3042f

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQdraw : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    Q.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨R, hQR, hRdraw, hRcard⟩ :=
    WilliamsonShmoys.planar_drawing_extends_to_triangulation Q hV hQdraw
  have hRQ : R = Q := hmax R hQR hRdraw
  rw [← hRQ]
  exact hRcard