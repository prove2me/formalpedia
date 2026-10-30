-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_for_completion_20261026
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:21:52.677627+00:00
-- url     : https://prove2.me/submissions/56ff16cc-990c-4084-bdb5-d3a18297f851

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_count_upper_bound_20261026
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_augmentation_20261026

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ N : SimpleGraph V, M ≤ N →
      WilliamsonShmoys.HasPlanarDrawingOn N → N = M) :
    M.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  have hup :
      M.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_drawing_edge_count_upper_bound_20261026 M hM hV
  by_contra hne
  have hlt : M.edgeSet.ncard < 3 * Fintype.card V - 6 := by omega
  obtain ⟨N, hMN, hNM, hN⟩ :=
    WilliamsonShmoys.planar_drawing_edge_augmentation_20261026 M hM hV hlt
  exact hNM (hmax N hMN hN)