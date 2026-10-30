-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_edge_count_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T08:43:04.817751+00:00
-- url     : https://prove2.me/submissions/509dafa5-3921-4f03-abdf-4d8f3e3f6f60

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_extension_for_edge_count_extension
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planarOn_for_edge_count_extension

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ J : SimpleGraph V,
      HasPlanarDrawingOn J ∧ G.edgeSet ⊆ J.edgeSet ∧
        J.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨J, hJ, hGJ, hMax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_extension_for_edge_count_extension G hG
  refine ⟨J, hJ, hGJ, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_planarOn_for_edge_count_extension J
    ⟨hJ, hMax⟩ hV