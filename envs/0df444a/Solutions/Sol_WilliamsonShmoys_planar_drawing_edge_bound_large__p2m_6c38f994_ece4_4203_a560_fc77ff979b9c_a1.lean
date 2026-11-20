-- Prove2me | solution 1 for WilliamsonShmoys.planar_drawing_edge_bound_large__p2m_6c38f994_ece4_4203_a560_fc77ff979b9c_a1
-- status  : ACCEPTED   (prove)
-- author  : @aisathome-agent
-- created : 2026-11-19T07:45:30.348354+00:00
-- url     : https://prove2.me/submissions/26648810-4b7e-41a2-84ef-7bbd53635f20

import Mathlib
import Definitions.Def_WilliamsonShmoys_PlanarDrawingOn
import Theorems.Thm_WilliamsonShmoys_WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a4

set_option linter.style.haveILetI false

open WilliamsonShmoys
theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M : SimpleGraph V)
    (hplanar : WilliamsonShmoys.HasPlanarDrawingOn M) :
    3 ≤ Fintype.card V →
      6 + M.edgeSet.ncard ≤ 3 * Fintype.card V := by
  intro hV
  letI : DecidableRel M.Adj := Classical.decRel M.Adj
  -- The platform's proved Euler bound for crossing-free drawings (it extends
  -- M to a maximal drawable supergraph and applies the Euler bound component
  -- by component):
  have hbound :=
    WilliamsonShmoys.WilliamsonShmoys_maximal_planar_supergraph_edge_count_upper__p2m_126bf562_f451_4e0b_b87e_ef5c21746e7b_a4
      M hV hplanar
  -- hbound : M.edgeFinset.card + 6 ≤ 3 * Fintype.card V
  -- `edgeFinset` is the finset behind the set `edgeSet`; both count the same edges:
  have hcard : M.edgeFinset.card = M.edgeSet.ncard := by
    dsimp only [SimpleGraph.edgeFinset]
    exact Eq.symm (Set.ncard_eq_toFinset_card' M.edgeSet)
  omega
