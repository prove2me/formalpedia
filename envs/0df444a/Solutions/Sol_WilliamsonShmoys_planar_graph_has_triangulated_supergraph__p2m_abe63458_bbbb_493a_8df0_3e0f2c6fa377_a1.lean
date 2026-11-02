-- Prove2me | solution 1 for WilliamsonShmoys.planar_graph_has_triangulated_supergraph__p2m_abe63458_bbbb_493a_8df0_3e0f2c6fa377_a1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T15:32:28.464146+00:00
-- url     : https://prove2.me/submissions/a0a66053-b491-4dbe-8dab-79d2093bef15
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_graph_has_maximal_planar_supergraph__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_graph_has_three_n_minus_six_edges__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1
import Mathlib

open WilliamsonShmoys

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) (hV : 3 ≤ Fintype.card V)
    (hH : HasPlanarDrawingOn H) :
    ∃ K : SimpleGraph V, H ≤ K ∧ HasPlanarDrawingOn K ∧
      (letI : DecidableRel K.Adj := Classical.decRel K.Adj
       3 * Fintype.card V = K.edgeFinset.card + 6) := by
  obtain ⟨K, hHK, hK, hmax⟩ :=
    WilliamsonShmoys.planar_graph_has_maximal_planar_supergraph__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1 H hH
  refine ⟨K, hHK, hK, ?_⟩
  exact WilliamsonShmoys.maximal_planar_graph_has_three_n_minus_six_edges__p2m_b8daf038_e3c0_4a60_b7f6_5a7661d4dadb_a1 K hV hK hmax