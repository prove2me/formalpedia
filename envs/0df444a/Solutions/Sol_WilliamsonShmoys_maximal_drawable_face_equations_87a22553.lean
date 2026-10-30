-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_face_equations_87a22553
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:17:20.240316+00:00
-- url     : https://prove2.me/submissions/ce50cc99-9026-4b2a-af4d-38bc12572449

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_triangulation_extension_87a22553
set_option autoImplicit false

/-- The maximality hypothesis identifies the given graph with a triangulated extension;
its edge count then yields the Euler and face-incidence equations. -/
theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    ∃ f : ℕ, Fintype.card V + f = H.edgeSet.ncard + 2 ∧
      3 * f = 2 * H.edgeSet.ncard := by
  obtain ⟨K, hHK, hKdraw, hKedges⟩ :=
    WilliamsonShmoys.maximal_drawable_triangulation_extension_87a22553 H hdraw hV
  have hKH : K ≤ H := hmax K hHK hKdraw
  have hEq : K = H := le_antisymm hKH hHK
  have hEdges : 3 * Fintype.card V = H.edgeSet.ncard + 6 := by
    simpa [hEq] using hKedges
  refine ⟨2 * Fintype.card V - 4, ?_, ?_⟩ <;> omega