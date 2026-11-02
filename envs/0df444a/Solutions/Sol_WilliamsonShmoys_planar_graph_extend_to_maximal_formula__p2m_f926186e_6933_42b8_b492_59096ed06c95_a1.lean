-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_extend_to_maximal_formula__p2m_f926186e_6933_42b8_b492_59096ed06c95_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:51:10.861989+00:00
-- url     : https://prove2.me/submissions/97bd1437-25f4-48d0-9101-02358c4cd62f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
import Mathlib

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hM : HasPlanarDrawingOn M)
    (hcard : 3 ≤ Fintype.card V) :
    ∃ N : SimpleGraph V, M ≤ N ∧ HasPlanarDrawingOn N ∧
      (letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
        fun K => Classical.decRel K.Adj
       N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
      M hM hcard
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_c6e7e4d2_ca9d_4ea4_bf6c_d30cb8b5a12f_a2
    N hN hcard hmax