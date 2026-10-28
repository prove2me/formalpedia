-- Prove2me | solution 1 for WilliamsonShmoys.sharp_planar_drawing_has_triangle_face_system
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:01:43.985792+00:00
-- url     : https://prove2.me/submissions/f3c90b99-59a8-4b3b-9364-16fcc55bf083
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Definitions.Def_WilliamsonShmoys_TriangularPlaneFaceSystem
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation_supergraph
import Theorems.Thm_WilliamsonShmoys_sharp_subgraph_of_sharp_planar_graph_eq

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hedge : H.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    ∃ faces : Multiset (Finset V),
      (∀ f, f ∈ faces → f.card = 3) ∧
      (∀ f, f ∈ faces → ∀ u, u ∈ f → ∀ v, v ∈ f →
        u ≠ v → H.Adj u v) ∧
      (∀ u v, H.Adj u v →
        (faces.filter (fun f => u ∈ f ∧ v ∈ f)).card = 2) := by
  obtain ⟨K, hHK, hKplanar, hKedge, hKfaces⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation_supergraph H hV hH
  have hEq : H = K :=
    WilliamsonShmoys.sharp_subgraph_of_sharp_planar_graph_eq H K hHK hedge hKedge
  subst K
  rcases hKfaces with ⟨faces, hcard, hadj, hedge_faces, _⟩
  exact ⟨faces, hcard, hadj, hedge_faces⟩