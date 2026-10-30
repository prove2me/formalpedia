-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_edge_count_extension_f663d05c
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T00:28:45.346629+00:00
-- url     : https://prove2.me/submissions/7fcae269-8f4f-461a-a90c-21c975c3c85c

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_edge_maximal_extension_f663d05c
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_f663d05c

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V = L.edgeSet.ncard + 6 := by
  obtain ⟨L, hGL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_edge_maximal_extension_f663d05c G hG
  refine ⟨L, hGL, hL, ?_⟩
  exact (WilliamsonShmoys.maximal_planar_edge_count_f663d05c L hL hV hmax).symm
