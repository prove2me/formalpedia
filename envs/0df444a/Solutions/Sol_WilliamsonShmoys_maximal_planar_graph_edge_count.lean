-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_graph_edge_count
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T01:05:37.700166+00:00
-- url     : https://prove2.me/submissions/a3d5ab84-f791-4a96-bc92-48b6695d0c28
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_extension

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V)
    (hH : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMax : ∀ K : SimpleGraph V, H ≤ K → WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    H.edgeSet.ncard = 3 * Fintype.card V - 6 := by
  obtain ⟨K, hHK, hK, hEdges⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_extension H hH hV
  have hKH : K ≤ H := hMax K hHK hK
  have hEq : H = K := le_antisymm hHK hKH
  simpa [hEq] using hEdges