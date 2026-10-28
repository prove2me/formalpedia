-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_ctx816e1e7
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T04:07:27.281977+00:00
-- url     : https://prove2.me/submissions/f67c3b91-f802-4b8c-8023-2cc8f6919ac1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_completion_edge_count_ctx816e1e7

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      Q ≤ R → WilliamsonShmoys.HasPlanarDrawingOn R → R = Q) :
    Q.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨R, hQR, hR, hcount⟩ :=
    WilliamsonShmoys.planar_completion_edge_count_ctx816e1e7 Q hV hQ
  have hRQ : R = Q := hmax R hQR hR
  rw [← hRQ]
  exact hcount