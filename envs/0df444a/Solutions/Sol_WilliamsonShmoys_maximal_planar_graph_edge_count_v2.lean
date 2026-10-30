-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:55:37.347583+00:00
-- url     : https://prove2.me/submissions/dc72b0c8-56c3-4d6e-98bf-980d80c5b303

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_triangulation_extension_for_edge_count_v2

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Q : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hQ : WilliamsonShmoys.HasPlanarDrawingOn Q)
    (hmax : ∀ R : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn R →
      Set.Subset Q.edgeSet R.edgeSet →
      R.edgeSet = Q.edgeSet) :
    3 * Fintype.card V ≤ Q.edgeSet.ncard + 6 := by
  obtain ⟨R, hR, hQR, hEdges⟩ :=
    WilliamsonShmoys.maximal_planar_graph_triangulation_extension_for_edge_count_v2
      Q hCard hQ
  have hEq := hmax R hR hQR
  rw [hEq] at hEdges
  omega