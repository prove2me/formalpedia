-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_triangular_plane_map
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T19:34:23.730179+00:00
-- url     : https://prove2.me/submissions/262b2d11-e48c-406e-8bc2-bec3022c8e60
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_has_triangular_faces__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
import Theorems.Thm_WilliamsonShmoys_finite_face_incidence_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a4
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hMax : ∀ M : SimpleGraph V,
      Set.Subset L.edgeSet M.edgeSet →
      WilliamsonShmoys.HasPlanarDrawingOn M →
      Set.Subset M.edgeSet L.edgeSet)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ (F : Type) (faceInst : Fintype F)
      (boundary : F → Finset (Sym2 V)),
      (∀ f, (boundary f).card = 3) ∧
      (∀ f, ∀ e ∈ boundary f, e ∈ L.edgeSet) ∧
      (∀ e ∈ L.edgeSet,
        ((@Finset.univ F faceInst).filter (fun f => e ∈ boundary f)).card = 2) ∧
      Fintype.card V + @Fintype.card F faceInst = L.edgeSet.ncard + 2 := by
  obtain ⟨F, faceInst, boundary, hFaces, hBoundary, hIncidence⟩ :=
    WilliamsonShmoys.maximal_planar_drawing_has_triangular_faces__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
      L hL hMax hCard
  letI : Fintype F := faceInst
  have hCount :=
    WilliamsonShmoys.finite_face_incidence_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a4
      (F := F) (E := Sym2 V) (edges := L.edgeSet) boundary
      hFaces hBoundary hIncidence
  have hEdgeCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_a8a0f1d5_6f00_4634_a5ce_7524a9f9c8af_a2
      L hL hMax hCard
  refine ⟨F, faceInst, boundary, hFaces, hBoundary, hIncidence, ?_⟩
  omega