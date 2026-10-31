-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulated_supergraph__p2m_03e1b202_06dc_4da5_bd81_d67a28c40fa1_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:51:50.42128+00:00
-- url     : https://prove2.me/submissions/e5f58d38-2dfa-495a-9989-d479dc5cdfd0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_to_edge_maximal__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V) (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      (∀ u v, G.Adj u v → K.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hKdraw, hKmax⟩ :=
    WilliamsonShmoys.planar_supergraph_to_edge_maximal__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
      G hG
  exact ⟨K, hGK, hKdraw,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_c77f60cb_52bf_4945_9bde_3c0cc2df12db_a2
      K hKdraw hKmax hV⟩