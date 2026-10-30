-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count_eq_euler_fd4411d1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:30:20.2427+00:00
-- url     : https://prove2.me/submissions/52721c3e-50c5-4d33-a7de-ba58d0f7bab4

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawing_has_triangulation

set_option autoImplicit false

open WilliamsonShmoys

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hH : HasPlanarDrawingOn H)
    (hcard : 3 ≤ Fintype.card V)
    (hmax : ∀ J : SimpleGraph V, H ≤ J → HasPlanarDrawingOn J → J ≤ H) :
    3 * Fintype.card V = H.edgeSet.ncard + 6 := by
  obtain ⟨J, hHJ, hJdraw, hcount⟩ :=
    WilliamsonShmoys.planar_drawing_has_triangulation H hH hcard
  have hJH : J ≤ H := hmax J hHJ hJdraw
  have hEq : H = J := le_antisymm hHJ hJH
  simpa [hEq] using hcount