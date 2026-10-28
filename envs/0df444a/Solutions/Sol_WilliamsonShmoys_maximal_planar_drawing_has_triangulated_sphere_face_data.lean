-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangulated_sphere_face_data
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T07:33:28.278932+00:00
-- url     : https://prove2.me/submissions/4872b552-4d0c-469d-a995-57ed2bbf2e29
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_PlanarTriangulationEulerData
import Theorems.Thm_WilliamsonShmoys_planar_drawing_admits_triangulated_planar_supergraph

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ H : SimpleGraph V, L ≤ H →
      WilliamsonShmoys.HasPlanarDrawingOn H → H ≤ L) :
    Nonempty (WilliamsonShmoys.TriangulatedSphereFaceData L) := by
  obtain ⟨H, hLH, hH, ⟨faces⟩⟩ :=
    WilliamsonShmoys.planar_drawing_admits_triangulated_planar_supergraph
      L hL hCard
  have hHL : H ≤ L := hMax H hLH hH
  have hEq : H = L := le_antisymm hHL hLH
  subst H
  exact ⟨faces⟩
