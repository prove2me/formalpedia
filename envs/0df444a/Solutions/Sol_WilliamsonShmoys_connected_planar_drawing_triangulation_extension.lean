-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_triangulation_extension
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T22:10:21.095657+00:00
-- url     : https://prove2.me/submissions/cdb423eb-6a60-416b-b82e-d882333f42c0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_exists_maximal_supergraph
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_edge_count_maximal
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawing_triangulation_edgeSet_ncard_mono

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hConnected : G.Connected)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      (∀ ⦃u v⦄, G.Adj u v → H.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H ∧
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      H.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨H, hGH, hH, hMax⟩ :=
    WilliamsonShmoys.connected_planar_drawing_triangulation_exists_maximal_supergraph G hG
  refine ⟨H, hGH, hH, ?_, ?_⟩
  · exact WilliamsonShmoys.connected_planar_drawing_triangulation_edgeSet_ncard_mono G H hGH
  · exact WilliamsonShmoys.connected_planar_drawing_triangulation_edge_count_maximal H hH hV hMax