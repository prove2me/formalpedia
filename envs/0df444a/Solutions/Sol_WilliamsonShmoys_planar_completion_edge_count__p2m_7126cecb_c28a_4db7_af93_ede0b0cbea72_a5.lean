-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_edge_count__p2m_7126cecb_c28a_4db7_af93_ede0b0cbea72_a5
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T12:46:25.550922+00:00
-- url     : https://prove2.me/submissions/0c66fee6-7969-44e5-9beb-7f050a48336d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_exists_maximal_planar_supergraph__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_supergraph_edge_count__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (G : SimpleGraph V)
    (hG : WilliamsonShmoys.HasPlanarDrawingOn G)
    (hV : 3 ≤ Fintype.card V) :
    ∃ K : SimpleGraph V,
      Set.Subset G.edgeSet K.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn K ∧
      K.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨K, hGK, hK, hmax⟩ :=
    WilliamsonShmoys.exists_maximal_planar_supergraph__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
      G hG
  refine ⟨K, hGK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_supergraph_edge_count__p2m_8895f479_77a0_4c1e_903f_b3af7ab1e8bd_a1
    K hK hV hmax