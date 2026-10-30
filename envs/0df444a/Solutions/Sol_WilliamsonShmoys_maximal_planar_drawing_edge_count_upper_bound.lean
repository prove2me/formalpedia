-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_edge_count_upper_bound
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T06:40:32.064915+00:00
-- url     : https://prove2.me/submissions/d88240e0-ad88-4ee5-bcb7-db0728529ea2

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_maximal_supergraph_for_edge_bound_v2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawing_edge_count_for_edge_bound_v2
import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_mono_for_edge_bound_v2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V) : H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hHK, hPlanar, hMax⟩ :=
    WilliamsonShmoys.planar_drawing_has_maximal_supergraph_for_edge_bound_v2 H hDrawing hV
  have hBound := WilliamsonShmoys.maximal_planar_drawing_edge_count_for_edge_bound_v2
    K hPlanar hV hMax
  have hMono := WilliamsonShmoys.edgeSet_ncard_mono_for_edge_bound_v2 H K hHK
  omega
