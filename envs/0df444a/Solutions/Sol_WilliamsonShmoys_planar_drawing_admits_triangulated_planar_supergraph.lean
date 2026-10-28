-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_admits_triangulated_planar_supergraph
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T08:08:11.245834+00:00
-- url     : https://prove2.me/submissions/7b43ec57-4ed8-48f2-bee5-8bd0fc76d9b5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_planar_supergraph
import Theorems.Thm_WilliamsonShmoys_maximal_planar_has_triangulated_sphere_face_data

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      L ≤ H ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData H) := by
  obtain ⟨H, hLH, hH, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_planar_supergraph L hL hCard
  exact ⟨H, hLH, hH,
    WilliamsonShmoys.maximal_planar_has_triangulated_sphere_face_data H hH hCard hmax⟩