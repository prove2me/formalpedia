-- Prove2me | solution 1 for WilliamsonShmoys.planar_simple_graph_edge_count_upper_bound
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T08:03:23.635944+00:00
-- url     : https://prove2.me/submissions/31fe0852-6c52-417c-9c9a-50890ff1df66
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph_6009196b_f86b_4d84_8003_efa7e8eeee60
import Theorems.Thm_WilliamsonShmoys_maximal_planar_face_decomposition_6009196b_f86b_4d84_8003_efa7e8eeee60
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hCard : 3 ≤ Fintype.card V) :
    (G.edgeSet.ncard : Int) ≤ 3 * (Fintype.card V : Int) - 6 := by
  obtain ⟨M, hGM, hM, hMax, hEdgeCount⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph_6009196b_f86b_4d84_8003_efa7e8eeee60 G hG
  obtain ⟨f, hEuler, hFaces⟩ :=
    WilliamsonShmoys.maximal_planar_face_decomposition_6009196b_f86b_4d84_8003_efa7e8eeee60 M hM hMax hCard
  have hEqNat : M.edgeSet.ncard + 6 = 3 * Fintype.card V := by
    omega
  have hEqInt : (M.edgeSet.ncard : Int) + 6 = 3 * (Fintype.card V : Int) := by
    exact_mod_cast hEqNat
  have hEdgeInt : (G.edgeSet.ncard : Int) ≤ (M.edgeSet.ncard : Int) := by
    exact_mod_cast hEdgeCount
  omega
