-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph_a8cccb55
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T15:04:59.417166+00:00
-- url     : https://prove2.me/submissions/17241db6-f93b-4bd7-a274-ba68ac7a5f26

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Set.Card
import Theorems.Thm_WilliamsonShmoys_finite_connected_supergraph_from_one_step
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_edge_between_components_card_three_a1fa2dac

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (W : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hW : WilliamsonShmoys.HasPlanarDrawingOn W) :
    ∃ H : SimpleGraph V,
      (W.edgeSet.ncard <= H.edgeSet.ncard /\
       H.Connected /\ WilliamsonShmoys.HasPlanarDrawingOn H) := by
  obtain ⟨H, hWH, hConn, hPlanar⟩ :=
    WilliamsonShmoys.finite_connected_supergraph_from_one_step
      (V := V) (W := W) (P := WilliamsonShmoys.HasPlanarDrawingOn)
      hW
      (by
        intro G hWG hGPlanar hGDisconnected
        exact WilliamsonShmoys.planar_drawing_add_edge_between_components_card_three_a1fa2dac
          (V := V) G hV hGPlanar hGDisconnected)
  refine ⟨H, ?_, hConn, hPlanar⟩
  exact Set.ncard_mono (SimpleGraph.edgeSet_subset_edgeSet.mpr hWH)
