-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_connected_extension_with_edge_mono
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T05:13:05.700405+00:00
-- url     : https://prove2.me/submissions/9771879a-6e58-4ca9-a9bc-33f851918545

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_planar_drawing_connected_extension_exists

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (Y : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hY : WilliamsonShmoys.HasPlanarDrawingOn Y) :
    ∃ Z : SimpleGraph V,
      Y ≤ Z ∧ Z.Connected ∧ WilliamsonShmoys.HasPlanarDrawingOn Z ∧
        Y.edgeSet.ncard ≤ Z.edgeSet.ncard := by
  obtain ⟨Z, hYZ, hconn, hdraw⟩ :=
    WilliamsonShmoys.planar_drawing_connected_extension_exists Y hV hY
  refine ⟨Z, hYZ, hconn, hdraw, ?_⟩
  exact Set.ncard_mono (SimpleGraph.edgeSet_mono hYZ)