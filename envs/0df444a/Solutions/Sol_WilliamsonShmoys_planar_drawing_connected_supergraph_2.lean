-- Prove2me | solution 2 for WilliamsonShmoys.planar_drawing_connected_supergraph
-- status  : ACCEPTED   (prove)
-- author  : @もち
-- created : 2026-11-24T04:24:15.725365+00:00
-- url     : https://prove2.me/submissions/1f7eaaa2-1d73-48a4-a65b-f2c1620e06c3

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_for_edge_bound_ef555edc
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_connected

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V,
      G.edgeSet.ncard ≤ H.edgeSet.ncard ∧
      (∀ u v : V, Nonempty (H.Walk u v)) ∧
      WilliamsonShmoys.HasPlanarDrawingOn H := by
  obtain ⟨H, -, hH, hle, hMax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_for_edge_bound_ef555edc G hG
  have hConn : H.Connected :=
    WilliamsonShmoys.maximal_planar_drawingOn_connected H hH hMax hV
  exact ⟨H, hle, fun u v => (hConn.preconnected u v), hH⟩
