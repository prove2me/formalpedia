-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:01:29.237781+00:00
-- url     : https://prove2.me/submissions/0757f69d-eb40-4729-8f48-f541f6d251e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_repair_3_planar_upper_edge_bound
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_repair_3_maximal_lower_edge_bound

set_option autoImplicit false

 theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N ∧
      (∀ H : SimpleGraph V, WilliamsonShmoys.HasPlanarDrawingOn H →
        N.edgeSet ⊆ H.edgeSet → H.edgeSet ⊆ N.edgeSet))
    (hV : 3 ≤ Fintype.card V) :
    3 * Fintype.card V = N.edgeSet.ncard + 6 := by
  have hup := WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3_planar_upper_edge_bound N hN.1 hV
  have hlo := WilliamsonShmoys.maximal_planar_drawingOn_edge_count_repair_3_maximal_lower_edge_bound N hN hV
  omega