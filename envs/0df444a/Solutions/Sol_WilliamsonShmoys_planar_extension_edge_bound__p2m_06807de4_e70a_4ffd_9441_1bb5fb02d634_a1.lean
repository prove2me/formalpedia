-- Prove2me | solution 1 for WilliamsonShmoys.planar_extension_edge_bound__p2m_06807de4_e70a_4ffd_9441_1bb5fb02d634_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T01:43:52.480219+00:00
-- url     : https://prove2.me/submissions/c283a0b1-44bb-427f-a8ea-4bfedad3ad7b
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hCard : 3 ≤ Fintype.card V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K) :
    ∃ L : SimpleGraph V,
      (∀ u v, K.Adj u v → L.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      3 * Fintype.card V ≤ L.edgeSet.ncard + 6 := by
  obtain ⟨M, hKM, hM, hMax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_extension__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
      K hK
  have hCount :=
    WilliamsonShmoys.maximal_planar_edge_count__p2m_4144dd03_670b_4445_9630_6cae19c82121_a1
      M hM hCard hMax
  refine ⟨M, hKM, hM, ?_⟩
  exact le_of_eq hCount