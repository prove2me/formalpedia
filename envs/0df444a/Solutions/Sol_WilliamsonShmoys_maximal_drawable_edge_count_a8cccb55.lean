-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_edge_count_a8cccb55
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:05:55.064985+00:00
-- url     : https://prove2.me/submissions/5b4d774c-3e63-4729-96e1-d32de3eaee30
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_has_triangulated_euler_certificate
import Theorems.Thm_WilliamsonShmoys_triangulated_euler_certificate_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (U : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hU : WilliamsonShmoys.HasPlanarDrawingOn U)
    (hmax : ∀ X : SimpleGraph V,
      U ≤ X → WilliamsonShmoys.HasPlanarDrawingOn X → X = U) :
    U.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  have hcert := WilliamsonShmoys.maximal_drawable_has_triangulated_euler_certificate
    U hV hU hmax
  exact WilliamsonShmoys.triangulated_euler_certificate_edge_count U hcert