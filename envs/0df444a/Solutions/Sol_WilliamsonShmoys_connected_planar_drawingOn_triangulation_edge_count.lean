-- Prove2me | solution 1 for WilliamsonShmoys.connected_planar_drawingOn_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:56:04.647024+00:00
-- url     : https://prove2.me/submissions/a8c244aa-ed31-4ee3-8388-6d02e67f9b95

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_connected_planar_drawingOn_maximal_extension
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_exact_edge_count

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hV : 3 <= Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hconn : K.Connected) :
    ∃ L : SimpleGraph V,
      K <= L ∧ WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V - 6 = L.edgeSet.ncard := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.connected_planar_drawingOn_maximal_extension K hK
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_drawingOn_exact_edge_count L hV hL
      (hconn.mono hKL) hmax⟩