-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangular_face_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:11:20.404067+00:00
-- url     : https://prove2.me/submissions/99d95399-1921-4d7a-9192-dd24f5160a98
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : forall H' : SimpleGraph V, H < H' ->
      ¬ (WilliamsonShmoys.HasPlanarDrawingOn H')) :
    WilliamsonShmoys.HasTriangularPlaneFaceSystem H := by
  obtain ⟨H', hle, hH', htri⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_completion H hV hconn hH
  have heq : H' = H := by
    by_contra hne
    have hlt : H < H' := lt_of_le_of_ne hle (Ne.symm hne)
    exact (hmax H' hlt) hH'
  simpa [heq] using htri