-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_bound_from_drawing
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T22:16:33.62973+00:00
-- url     : https://prove2.me/submissions/64655e4f-04fc-4e3a-a283-7b36625bbf76

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_extension_fixed_vertex_set
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_euler_augmentation

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hDraw : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      G.edgeSet ⊆ K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V ≤ K.edgeSet.ncard + 6 := by
  obtain ⟨K, hsub, hDrawK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_extension_fixed_vertex_set G hDraw
  have hbound :=
    WilliamsonShmoys.maximal_planar_edge_bound_euler_augmentation K hDrawK hCard hmax
  exact ⟨K, hsub, hDrawK, hbound⟩