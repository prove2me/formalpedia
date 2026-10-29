-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_face_count_certificate
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T02:56:22.145926+00:00
-- url     : https://prove2.me/submissions/0610e610-9c93-48f9-b723-cfe41f07bfe7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_for_face_count_certificate

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hMax : ∀ J : SimpleGraph V,
      H ≤ J → WilliamsonShmoys.HasPlanarDrawingOn J → J ≤ H) :
    ∃ f : ℕ,
      Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by
  have hEdges :=
    WilliamsonShmoys.maximal_planar_edge_count_for_face_count_certificate
      H hV hH hMax
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega