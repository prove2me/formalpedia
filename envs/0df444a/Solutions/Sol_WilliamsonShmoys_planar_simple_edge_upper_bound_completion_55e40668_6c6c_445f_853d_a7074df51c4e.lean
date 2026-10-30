-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_edge_upper_bound_completion_55e40668_6c6c_445f_853d_a7074df51c4e
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:44:55.464837+00:00
-- url     : https://prove2.me/submissions/bae20879-50a1-42f5-b65e-14512c2e7830

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_triangulation_extension

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hV : 3 ≤ Fintype.card V) :
    L.edgeSet.ncard ≤ 3 * Fintype.card V - 6 := by
  obtain ⟨H, hLH, _hHplanar, hHcard⟩ :=
    WilliamsonShmoys.planar_drawing_triangulation_extension L hL hV
  have hsub : L.edgeSet ⊆ H.edgeSet :=
    (SimpleGraph.edgeSet_subset_edgeSet).2 hLH
  calc
    L.edgeSet.ncard ≤ H.edgeSet.ncard := Set.ncard_le_ncard hsub
    _ = 3 * Fintype.card V - 6 := hHcard