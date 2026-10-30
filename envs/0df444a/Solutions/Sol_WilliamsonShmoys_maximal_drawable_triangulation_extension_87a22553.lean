-- Prove2me | solution 1 for WilliamsonShmoys.maximal_drawable_triangulation_extension_87a22553
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:50:03.183425+00:00
-- url     : https://prove2.me/submissions/910b7904-c4b1-473f-bbbb-6bac00015ba8

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_extension_d974173a
import Theorems.Thm_WilliamsonShmoys_maximal_drawable_edge_count_d974173a

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hdraw : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V, H ≤ K ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      3 * Fintype.card V = K.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_extension_d974173a H hdraw
  exact ⟨K, hHK, hKdraw,
    WilliamsonShmoys.maximal_drawable_edge_count_d974173a K hKdraw hV hKmax⟩