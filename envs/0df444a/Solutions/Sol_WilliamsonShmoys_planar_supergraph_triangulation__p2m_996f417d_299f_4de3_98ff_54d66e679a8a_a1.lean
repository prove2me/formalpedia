-- Prove2me | solution 1 for WilliamsonShmoys.planar_supergraph_triangulation__p2m_996f417d_299f_4de3_98ff_54d66e679a8a_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T04:40:31.283204+00:00
-- url     : https://prove2.me/submissions/e641865b-bee4-4f60-a370-2b276d84b8df
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
import Theorems.Thm_WilliamsonShmoys_edge_count_of_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ W : SimpleGraph V, G ≤ W ∧ WilliamsonShmoys.HasPlanarDrawingOn W ∧
      W.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨W, hGW, hW, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1 G hG
  exact ⟨W, hGW, hW,
    WilliamsonShmoys.edge_count_of_maximal_drawable_supergraph__p2m_ceea82b2_e199_492c_ad5d_a194ae5752ca_a1 W hW hV hmax⟩