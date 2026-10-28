-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_add_edge_of_disconnected
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T09:50:20.023611+00:00
-- url     : https://prove2.me/submissions/ab4f73cf-22f6-4452-9c71-e5b12ef4a42d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Theorems.Thm_WilliamsonShmoys_disconnected_has_nonadjacent_vertices
import Theorems.Thm_WilliamsonShmoys_planar_drawing_add_selected_nonedge
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (X : SimpleGraph V)
    (hV : 3 ≤ Fintype.card V)
    (hX : WilliamsonShmoys.HasPlanarDrawingOn X)
    (hDisconnected : ¬ X.Connected) :
    ∃ Z : SimpleGraph V,
      X ≤ Z ∧
      X.edgeSet.ncard < Z.edgeSet.ncard ∧
      WilliamsonShmoys.HasPlanarDrawingOn Z := by
  obtain ⟨u, v, huv, hnot⟩ :=
    WilliamsonShmoys.disconnected_has_nonadjacent_vertices X hV hDisconnected
  obtain ⟨Z, hle, hcard, hdraw, hadj⟩ :=
    WilliamsonShmoys.planar_drawing_add_selected_nonedge X hX u v huv hnot
  exact ⟨Z, hle, hcard, hdraw⟩