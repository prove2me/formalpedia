-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound_9064c577
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-27T14:02:05.74966+00:00
-- url     : https://prove2.me/submissions/5f0bad93-84a1-4ab1-bddd-83b6df31c6af

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_triangulation_augmentation_9064c577

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hConn : H.Connected)
    (hDraw : HasPlanarDrawingOn H)
    (hCard : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → HasPlanarDrawingOn K → K = H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKDraw, hEdges⟩ :=
    WilliamsonShmoys.planar_graph_triangulation_augmentation_9064c577
      H hConn hDraw hCard
  have hEq : K = H := hMax K hHK hKDraw
  subst K
  omega