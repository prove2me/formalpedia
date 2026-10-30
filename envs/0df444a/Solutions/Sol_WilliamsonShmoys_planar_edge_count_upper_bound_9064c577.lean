-- Prove2me | solution 1 for WilliamsonShmoys.planar_edge_count_upper_bound_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:29:41.97763+00:00
-- url     : https://prove2.me/submissions/5ad8fcb5-7b0a-42ce-99ff-35144970b476

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_maximal_extension_for_edge_bound_9064c577
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_bound_9064c577

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V) :
    H.edgeSet.ncard + 6 ≤ 3 * Fintype.card V := by
  obtain ⟨K, hSub, hKConn, hKDraw, hMax, hEdgeCount⟩ :=
    WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound_9064c577 H hConn hDraw
  have hKBound := WilliamsonShmoys.maximal_planar_edge_bound_9064c577
    K hKConn hKDraw hCard hMax
  omega