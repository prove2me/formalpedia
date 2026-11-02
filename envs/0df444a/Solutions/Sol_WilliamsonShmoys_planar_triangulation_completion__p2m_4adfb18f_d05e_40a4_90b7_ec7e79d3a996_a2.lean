-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_4adfb18f_d05e_40a4_90b7_ec7e79d3a996_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:55:41.93187+00:00
-- url     : https://prove2.me/submissions/93d0c9d9-5f1d-4d7b-b27a-90330a665097
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_edge_count__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hcard : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V = P.edgeSet.ncard + 6 := by
  obtain ⟨P, hNP, hP, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_supergraph__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3 N hN
  exact ⟨P, hNP, hP,
    WilliamsonShmoys.maximal_planar_graph_edge_count__p2m_c8fc71ba_c41f_4610_9114_f9df2f968aaf_a3 P hcard hP hmax⟩