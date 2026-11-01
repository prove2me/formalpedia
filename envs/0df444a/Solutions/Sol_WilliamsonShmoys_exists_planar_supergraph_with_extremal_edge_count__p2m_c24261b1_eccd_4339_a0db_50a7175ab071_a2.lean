-- Prove2me | solution 1 for WilliamsonShmoys.exists_planar_supergraph_with_extremal_edge_count__p2m_c24261b1_eccd_4339_a0db_50a7175ab071_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:35:45.919686+00:00
-- url     : https://prove2.me/submissions/1017f931-58d5-491f-b056-7b5554712bb5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : HasPlanarDrawingOn G)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ H : SimpleGraph V, G ≤ H ∧ HasPlanarDrawingOn H ∧
      (letI : DecidableRel H.Adj := Classical.decRel H.Adj;
        H.edgeFinset.card = 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨H, hGH, hH, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1 G hG
  have hedge :=
    WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_99da7898_0d3e_41e3_bad9_9b286d32e26c_a1 H hH hcard hmax
  exact ⟨H, hGH, hH, hedge⟩