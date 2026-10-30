-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_292cccde_9238_49dd_bff4_dbc6d5d73c71_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-29T18:30:41.761708+00:00
-- url     : https://prove2.me/submissions/a9faba59-14f4-41c3-b0ab-6b64df82f180
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_supergraph_maximal__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (K : SimpleGraph V)
    (hK : WilliamsonShmoys.HasPlanarDrawingOn K)
    (hV : 3 ≤ Fintype.card V) :
    ∃ L : SimpleGraph V,
      Set.Subset K.edgeSet L.edgeSet ∧
      WilliamsonShmoys.HasPlanarDrawingOn L ∧
      L.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨L, hKL, hL, hmax⟩ :=
    WilliamsonShmoys.planar_supergraph_maximal__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
      K hK hV
  exact ⟨L, hKL, hL,
    WilliamsonShmoys.maximal_planar_edge_count__p2m_fddb0f81_7944_4e99_898d_d807c45592e3_a1
      L hV hL hmax⟩
