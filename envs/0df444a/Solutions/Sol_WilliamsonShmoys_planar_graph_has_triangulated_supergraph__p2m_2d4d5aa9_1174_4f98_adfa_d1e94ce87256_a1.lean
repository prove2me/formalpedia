-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_2d4d5aa9_1174_4f98_adfa_d1e94ce87256_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T02:52:17.910515+00:00
-- url     : https://prove2.me/submissions/5de53da1-3671-4c40-9b72-abee3a7b3dd5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_triangulated_supergraph_maximal__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_three_n_minus_six_edges__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V)
    (hN : WilliamsonShmoys.HasPlanarDrawingOn N)
    (hcard : 3 <= Fintype.card V) :
    ∃ P : SimpleGraph V,
      WilliamsonShmoys.HasPlanarDrawingOn P ∧
      (∀ u v, N.Adj u v → P.Adj u v) ∧
      P.edgeSet.ncard + 6 = 3 * Fintype.card V := by
  obtain ⟨P, hP, hsub, hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_triangulated_supergraph_maximal__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
      N hN hcard
  exact ⟨P, hP, hsub,
    WilliamsonShmoys.maximal_planar_graph_has_three_n_minus_six_edges__p2m_742ffe8a_7b30_4bb8_be55_29e8d8d53fed_a1
      P hP hcard hmax⟩