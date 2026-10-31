-- Prove2me | solution 1 for WilliamsonShmoys.simple_planar_drawing_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:28:06.974999+00:00
-- url     : https://prove2.me/submissions/c3ee6a54-3e91-48b1-9c42-f257c26bd10b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_augmentation
import Theorems.Thm_WilliamsonShmoys_connected_planar_edge_count_upper_bound

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G) :
    G.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hGH, hConnected, hPlanar, hEdges⟩ :=
    WilliamsonShmoys.connected_planar_augmentation G hV hG
  have hUpper :=
    WilliamsonShmoys.connected_planar_edge_count_upper_bound H hV hConnected hPlanar
  exact hEdges.trans hUpper