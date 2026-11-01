-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_supergraph_exact_edge_count__p2m_00360c86_73a0_483f_8c2b_2f99e65d88dd_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T03:13:06.651299+00:00
-- url     : https://prove2.me/submissions/fc33a8ee-083c-4d02-9735-1ff35c7afca7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_exists_edge_maximal_planar_supergraph__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hM : HasPlanarDrawingOn M) :
    ∃ N : SimpleGraph V,
      M ≤ N ∧ HasPlanarDrawingOn N ∧
        (letI : DecidableRel N.Adj := Classical.decRel N.Adj;
          N.edgeFinset.card + 6 = 3 * Fintype.card V) := by
  obtain ⟨N, hMN, hN, hmax⟩ :=
    WilliamsonShmoys.exists_edge_maximal_planar_supergraph__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2 M hM
  refine ⟨N, hMN, hN, ?_⟩
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_a12109a5_f1ad_4ab6_9c6b_e3b453b2179d_a2 N hV hN hmax