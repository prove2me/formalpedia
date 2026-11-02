-- Prove2me | solution 1 for WilliamsonShmoys.planar_triangulation_completion__p2m_689940da_6233_467d_b487_080b0de38a3b_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:02:53.137202+00:00
-- url     : https://prove2.me/submissions/bcd7b0ac-969f-41a3-b6ca-6524b7741ca2

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_planar_maximal_supergraph__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1
import Mathlib

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hcard : 3 <= Fintype.card V) :
    ∃ Q : SimpleGraph V,
      (∀ {u v : V}, P.Adj u v → Q.Adj u v) ∧
      WilliamsonShmoys.HasPlanarDrawingOn Q ∧
      (letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
       3 * Fintype.card V = Q.edgeFinset.card + 6) := by
  obtain ⟨Q, hPQ, hQ, hmax⟩ :=
    WilliamsonShmoys.planar_maximal_supergraph__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1 P hP
  refine ⟨Q, hPQ, hQ, ?_⟩
  letI : DecidableRel Q.Adj := Classical.decRel Q.Adj
  exact WilliamsonShmoys.maximal_planar_edge_count__p2m_2d6ff097_7c5b_40ac_9dcb_907c25524093_a1 Q hcard hQ hmax