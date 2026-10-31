-- Prove2me | solution 1 for WilliamsonShmoys.planar_completion_euler_data__p2m_49196ac4_b46c_446f_b424_262126b1b13c_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:45:45.412226+00:00
-- url     : https://prove2.me/submissions/3b01b571-3fee-4cba-8ff9-05a23a50c86e

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib.Tactic
import Theorems.Thm_WilliamsonShmoys_planar_simple_graph_edge_bound__p2m_0ea129f4_3238_4899_8c4a_237a80d1c906_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] (R : SimpleGraph V)
    (hDraw : HasPlanarDrawingOn R) (hV : 3 ≤ Fintype.card V) :
    ∃ (m' f : ℕ), R.edgeSet.ncard ≤ m' ∧
      Fintype.card V + f = m' + 2 ∧ 3 * f ≤ 2 * m' := by
  classical
  have hEdge : R.edgeSet.ncard ≤ 3 * Fintype.card V - 6 :=
    WilliamsonShmoys.planar_simple_graph_edge_bound__p2m_0ea129f4_3238_4899_8c4a_237a80d1c906_a1
      R hDraw hV
  refine ⟨3 * Fintype.card V - 6, 2 * Fintype.card V - 4, hEdge, ?_, ?_⟩
  · omega
  · omega