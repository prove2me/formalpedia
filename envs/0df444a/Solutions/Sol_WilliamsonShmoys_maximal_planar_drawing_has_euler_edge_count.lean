-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_has_euler_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T07:30:51.354027+00:00
-- url     : https://prove2.me/submissions/0d701f8d-ef86-459b-94bf-3e4a8966ddfb

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_extends_to_triangulated_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hmax : ∀ K : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn K →
      L.edgeSet ⊆ K.edgeSet → K.edgeSet = L.edgeSet) :
    L.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hK, hsub, hcard⟩ :=
    WilliamsonShmoys.planar_drawing_extends_to_triangulated_edge_count L hV hL
  have hsets : K.edgeSet = L.edgeSet := hmax K hK hsub
  simpa [hsets] using hcard