-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_upper_bound__p2m_dcda2b2e_bb79_4b65_906a_4b43dfb1e747_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T13:08:17.295809+00:00
-- url     : https://prove2.me/submissions/b761c00e-ce49-42c4-9ec4-f7c330da2155

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_drawing_on_maximal_extension__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_drawing__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1

open WilliamsonShmoys
set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hcard : 3 ≤ Fintype.card V)
    (hN : HasPlanarDrawingOn N) :
    (letI : DecidableRel N.Adj := Classical.decRel N.Adj
     N.edgeFinset.card ≤ 3 * Fintype.card V - 6) := by
  classical
  obtain ⟨M, hNM, hM, hcount, hmax⟩ :=
    WilliamsonShmoys.planar_drawing_on_maximal_extension__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1 N hcard hN
  have hMcount := WilliamsonShmoys.edge_count_of_maximal_planar_drawing__p2m_92aefffa_7fe2_4e94_9c0b_6e84d250c255_a1 M hcard hM hmax
  exact le_trans hcount (le_of_eq hMcount)