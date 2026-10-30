-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_decomposition_aux
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T13:21:24.345529+00:00
-- url     : https://prove2.me/submissions/8e2133eb-0274-4c08-b785-d777d15517fb

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangulatedPlanarFaceData
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_data_of_drawing
import Theorems.Thm_WilliamsonShmoys_triangulated_face_data_counts

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by
  obtain ⟨D⟩ :=
    WilliamsonShmoys.maximal_planar_face_data_of_drawing H hH hmax hV
  exact WilliamsonShmoys.triangulated_face_data_counts D
