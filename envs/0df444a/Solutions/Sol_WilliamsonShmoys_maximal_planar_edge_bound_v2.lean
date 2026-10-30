-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T03:45:15.171846+00:00
-- url     : https://prove2.me/submissions/eb223878-4f0b-4f8b-9557-c606d1ffe62a

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawing_has_euler_face_count
import Theorems.Thm_WilliamsonShmoys_edge_bound_of_euler_face_count

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hmax : ∀ L : SimpleGraph V,
      K.edgeSet ⊆ L.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet ⊆ K.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨f, hEuler, hTri⟩ :=
    WilliamsonShmoys.maximal_drawing_has_euler_face_count K hK hmax hCard
  have hEq :=
    WilliamsonShmoys.edge_bound_of_euler_face_count K f hEuler hTri
  omega