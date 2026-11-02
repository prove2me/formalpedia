-- Prove2me | solution 1 for WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_c1b4f689_ce4a_40bb_ab72_071998d2bd64_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-02T01:56:57.221582+00:00
-- url     : https://prove2.me/submissions/459dd036-35c1-4e37-844b-eda5f822c6e7

import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Mathlib
import Theorems.Thm_WilliamsonShmoys_maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1

set_option autoImplicit false

open WilliamsonShmoys

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V)
    (hP : WilliamsonShmoys.HasPlanarDrawingOn P)
    (hmax : ∀ Q : SimpleGraph V, P ≤ Q →
      WilliamsonShmoys.HasPlanarDrawingOn Q → Q = P)
    (hcard : 3 ≤ Fintype.card V)
    [DecidableRel P.Adj] :
    3 * Fintype.card V ≤ P.edgeFinset.card + 6 := by
  have h := WilliamsonShmoys.maximal_planar_edge_count_lower_bound__p2m_7faa0883_91bf_4801_b0cf_9d9827720e15_a1
    P hcard hP hmax
  have hedge : P.edgeSet.ncard = P.edgeFinset.card := by
    rw [Set.ncard_eq_toFinset_card']
    rfl
  rw [← hedge]
  exact h
