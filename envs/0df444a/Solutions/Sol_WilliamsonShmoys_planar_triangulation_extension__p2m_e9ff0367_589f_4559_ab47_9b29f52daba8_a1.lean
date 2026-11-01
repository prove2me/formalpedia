-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_extension__p2m_e9ff0367_589f_4559_ab47_9b29f52daba8_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-31T21:05:08.123199+00:00
-- url     : https://prove2.me/submissions/731524f7-a05f-401d-9db4-67ded4cdb526
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WilliamsonShmoys_maximal_planar_extension__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V) (dL : DecidableRel L.Adj)
    (hL : WilliamsonShmoys.HasPlanarDrawingOn L)
    (hcard : 3 <= Fintype.card V) :
    ∃ (M : SimpleGraph V) (dM : DecidableRel M.Adj),
      WilliamsonShmoys.HasPlanarDrawingOn M ∧
      L.edgeFinset ⊆ M.edgeFinset ∧
      M.edgeFinset.card = 3 * Fintype.card V - 6 := by
  obtain ⟨M, dM, hM, hLM, hmax⟩ :=
    WilliamsonShmoys.maximal_planar_extension__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
      L dL hL
  refine ⟨M, dM, hM, hLM, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_ebf573df_7a41_4cc7_8e00_a5df5b7401f0_a2
    M dM hM hmax hcard