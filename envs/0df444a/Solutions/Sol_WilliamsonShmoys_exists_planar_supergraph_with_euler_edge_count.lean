-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_euler_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T04:15:48.445627+00:00
-- url     : https://prove2.me/submissions/b1146738-642b-4da4-8b07-5efdf2285e35

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_augmentation_exists_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_euler_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      H.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hcard, hmax⟩ :=
    WilliamsonShmoys.planar_augmentation_exists_maximal_extension H hV hH
  have hEuler :=
    WilliamsonShmoys.maximal_planar_graph_euler_edge_count K hV hK hmax
  exact ⟨K, hHK, hK, hcard, hEuler⟩