-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_has_triangulation_edge_count
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T00:17:34.967251+00:00
-- url     : https://prove2.me/submissions/b55b4d54-f700-401c-a63d-2d1227c150c0

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_edge_bound
import Theorems.Thm_WilliamsonShmoys_planar_drawingOn_triangulation_completion

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V)
    (hmax : ∀ L : SimpleGraph V, K ≤ L → WilliamsonShmoys.HasPlanarDrawingOn L →
      L.edgeSet.ncard ≤ K.edgeSet.ncard) :
    K.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨L, hKL, hL, hLE⟩ :=
    WilliamsonShmoys.planar_drawingOn_triangulation_completion K hK hV
  have hLK := hmax L hKL hL
  rw [hLE] at hLK
  have hUpper :=
    WilliamsonShmoys.planar_drawingOn_edge_bound K hK hV
  exact Nat.le_antisymm hUpper hLK