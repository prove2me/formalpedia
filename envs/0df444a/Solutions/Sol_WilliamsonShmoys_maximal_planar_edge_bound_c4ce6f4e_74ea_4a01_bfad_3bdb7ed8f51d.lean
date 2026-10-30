-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_bound_c4ce6f4e_74ea_4a01_bfad_3bdb7ed8f51d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T10:14:26.200091+00:00
-- url     : https://prove2.me/submissions/5165aa16-7b68-4a38-a422-b9f91b04b47a

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_aux

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K → H ≤ K → K ≤ H) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_aux H hH hmax hV
  omega