-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T18:48:58.25089+00:00
-- url     : https://prove2.me/submissions/50c06507-e27f-471d-badd-97229a059d6b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_completion_for_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 <= Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hmax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K = H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcount⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_completion_for_edge_count H hV hH
  have hKH : K = H := hmax K hHK hK
  rw [hKH] at hcount
  exact hcount
