-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_triangulation_extension_for_maximal_edge_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:36:00.957088+00:00
-- url     : https://prove2.me/submissions/8457a9da-51ec-43ee-88d9-da40b2126ac9

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_same_vertex_maximal_planar_augmentation_extension
import Theorems.Thm_WilliamsonShmoys_inclusion_maximal_planar_edge_count_euler

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.same_vertex_maximal_planar_augmentation_extension H hH hV
  exact ⟨K, hHK, hK,
    WilliamsonShmoys.inclusion_maximal_planar_edge_count_euler K hK hV hmax⟩