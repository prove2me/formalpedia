-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawing_completion_edge_count_9c238260_8e64_40d3_b87d_42af728950e9_maximal_edge_lower_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T05:51:01.415636+00:00
-- url     : https://prove2.me/submissions/56d5a954-c72c-43c6-a85e-a752c1ba9209
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_can_be_augmented_to_edge_count

open WilliamsonShmoys

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hDrawing : WilliamsonShmoys.HasPlanarDrawingOn H)
    (hV : 3 ≤ Fintype.card V)
    (hMaximal : ∀ K : SimpleGraph V, H ≤ K →
      WilliamsonShmoys.HasPlanarDrawingOn K → K ≤ H) :
    3 * Fintype.card V ≤ H.edgeSet.ncard + 6 := by
  obtain ⟨K, hHK, hKDrawing, hCount⟩ :=
    WilliamsonShmoys.planar_graph_can_be_augmented_to_edge_count H hDrawing hV
  have hKH : K ≤ H := hMaximal K hHK hKDrawing
  have hEq : K = H := le_antisymm hKH hHK
  rw [← hEq]
  omega