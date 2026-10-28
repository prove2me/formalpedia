-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_maximal_extension_for_edge_bound_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:58:50.330802+00:00
-- url     : https://prove2.me/submissions/1558cbcd-7eb0-4db8-89e3-7f6b6bfb0b0e

import Theorems.Thm_WilliamsonShmoys_finite_edge_maximal_planar_extension_9064c577
import Theorems.Thm_WilliamsonShmoys_supergraph_connected_edge_count_9064c577

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V,
      (∀ ⦃u v⦄, H.Adj u v → K.Adj u v) ∧
      K.Connected ∧
      HasPlanarDrawingOn K ∧
      (∀ L : SimpleGraph V,
        (∀ ⦃u v⦄, K.Adj u v → L.Adj u v) →
        HasPlanarDrawingOn L →
        ∀ ⦃u v⦄, L.Adj u v → K.Adj u v) ∧
      H.edgeSet.ncard ≤ K.edgeSet.ncard := by
  obtain ⟨K, hHK, hKDraw, hMax⟩ :=
    WilliamsonShmoys.finite_edge_maximal_planar_extension_9064c577 H hDraw
  obtain ⟨hKConn, hEdges⟩ :=
    WilliamsonShmoys.supergraph_connected_edge_count_9064c577 H K hConn hHK
  exact ⟨K, hHK, hKConn, hKDraw, hMax, hEdges⟩