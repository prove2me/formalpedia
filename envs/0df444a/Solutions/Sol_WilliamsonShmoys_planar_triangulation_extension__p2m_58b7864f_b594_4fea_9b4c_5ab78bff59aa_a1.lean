-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_58b7864f_b594_4fea_9b4c_5ab78bff59aa_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:26:34.710372+00:00
-- url     : https://prove2.me/submissions/85455644-3f52-4ece-a291-0931ae6d81c2
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_finite_maximal_planar_extension__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (dM : DecidableRel M.Adj)
    (hM : WilliamsonShmoys.HasPlanarDrawingOn M)
    (hcard : 3 <= Fintype.card V) :
    ∃ (N : SimpleGraph V) (dN : DecidableRel N.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn N ∧
      M.edgeFinset ⊆ N.edgeFinset ∧
      N.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨N, dN, hN, hMN, hmax⟩ :=
    WilliamsonShmoys.finite_maximal_planar_extension__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
      M dM hM hcard
  refine ⟨N, dN, hN, hMN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_10fbf93e_9f1f_430c_8d69_9a023f7a87fc_a1
    N dN hN hcard hmax