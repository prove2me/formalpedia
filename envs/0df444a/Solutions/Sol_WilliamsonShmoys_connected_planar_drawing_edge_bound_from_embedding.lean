-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawing_edge_bound_from_embedding
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T12:57:49.305998+00:00
-- url     : https://prove2.me/submissions/8ece73fe-9f9b-4248-b2f6-1b686e3cefe5

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_edge_bound_extension_core
import Theorems.Thm_WilliamsonShmoys_edge_count_le_of_tight_supergraph

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hConn : G.Connected)
    (hGdraw : HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    G.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨H, hGH, hHEq⟩ :=
    WilliamsonShmoys.planar_drawing_edge_bound_extension_core G hConn hGdraw hCard
  exact WilliamsonShmoys.edge_count_le_of_tight_supergraph hGH hHEq