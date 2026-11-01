-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count__p2m_9d0243ad_5518_4310_b6ca_96e7e23d454c_a2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:20:11.771068+00:00
-- url     : https://prove2.me/submissions/efeabd6b-53d5-42dd-9a63-3fe3eced212c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_planar_graph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N) :
    ∃ P : SimpleGraph V,
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      3 * Fintype.card V = P.edgeSet.ncard + 6 := by
  obtain ⟨P, hNP, hP, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
      N hN
  refine ⟨P, hNP, hP, ?_⟩
  exact WilliamsonShmoys.edge_count_of_maximal_planar_graph__p2m_102f4bfa_075e_4b5b_84e9_4b6c34bfa40c_a1
    P hV hP hmax