-- Prove2me | solution 1 for WilliamsonShmoys.component_edge_bounds__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:51:16.145945+00:00
-- url     : https://prove2.me/submissions/c8713d5d-02d6-400e-8151-5e246ad12e17
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_edge_bounds_small__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
import Theorems.Thm_WilliamsonShmoys_component_edge_bounds_large__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (L : SimpleGraph V)
    (hLocal : ∀ (S : Finset V), 3 ≤ S.card →
      (L.induce (↑S : Set V)).Connected →
      (L.induce (↑S : Set V)).edgeSet.ncard + 6 ≤ 3 * S.card) :
    (∀ c : L.ConnectedComponent,
      (SimpleGraph.ConnectedComponent.supp c).ncard ≤ 2 →
        (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard ≤ 1) ∧
    (∀ c : L.ConnectedComponent,
      3 ≤ (SimpleGraph.ConnectedComponent.supp c).ncard →
        (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard + 6 ≤
          3 * (SimpleGraph.ConnectedComponent.supp c).ncard) := by
  constructor
  · intro c hsmall
    exact WilliamsonShmoys.component_edge_bounds_small__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
      L c hsmall
  · intro c hlarge
    exact WilliamsonShmoys.component_edge_bounds_large__p2m_798c5648_bc79_4a8b_aaf2_40b61aa85372_a1
      L hLocal c hlarge