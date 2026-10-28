-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_completion
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:19:20.843+00:00
-- url     : https://prove2.me/submissions/3e86a3a1-324e-4d43-98b7-952c8825fa77
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_completion
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_triangular_face_system

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hconn : H.Connected)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    exists H' : SimpleGraph V,
      H <= H' ∧
      WilliamsonShmoys.HasPlanarDrawingOn H' ∧
      WilliamsonShmoys.HasTriangularPlaneFaceSystem H' := by
  obtain ⟨H', hHH', hH', hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_planar_completion H hV hconn hH
  exact ⟨H', hHH', hH',
    WilliamsonShmoys.maximal_planar_graph_has_triangular_face_system
      H' hV hH' hmax⟩