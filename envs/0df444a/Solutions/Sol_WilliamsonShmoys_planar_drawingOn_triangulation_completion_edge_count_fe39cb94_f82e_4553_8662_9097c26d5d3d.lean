-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawingOn_triangulation_completion_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T04:01:32.040021+00:00
-- url     : https://prove2.me/submissions/9fc8bef6-8887-4431-81b3-905b0040f3c3

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_drawable_supergraph_maximal_fe39cb94_f82e_4553_8662_9097c26d5d3d
import Theorems.Thm_WilliamsonShmoys_maximal_planar_drawingOn_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hCard : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      N.edgeSet ⊆ K.edgeSet ∧ WilliamsonShmoys.HasPlanarDrawingOn K ∧
      (K.edgeSet.ncard : Int) = 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨K, hNK, hK, hMax⟩ :=
    WilliamsonShmoys.drawable_supergraph_maximal_fe39cb94_f82e_4553_8662_9097c26d5d3d N hN
  refine ⟨K, hNK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_drawingOn_edge_count_fe39cb94_f82e_4553_8662_9097c26d5d3d K hK hCard hMax