-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_triangulation_lower_bound_v2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:44:54.96351+00:00
-- url     : https://prove2.me/submissions/cf645952-1ed3-4ade-bb37-7ee1314ae83b

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawingOn_triangulation_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected)
    (hmax : forall L : SimpleGraph V, K <= L ->
      WilliamsonShmoys.HasPlanarDrawingOn L -> L = K) :
    3 * Fintype.card V - 6 <= K.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hcount⟩ :=
    WilliamsonShmoys.connected_planar_drawingOn_triangulation_edge_count
      K hV hK hconn
  have hLK := hmax L hKL hL
  rw [← hLK]
  exact hcount.le