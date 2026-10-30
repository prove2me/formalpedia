-- Prove2me | solution 1 for WilliamsonShmoys.component_vertex_accounting__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a1__p2m_ddc73965_e52c_4f89_a584_0b5c76884424_a3
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T05:51:00.106321+00:00
-- url     : https://prove2.me/submissions/bb953ef4-270d-4926-9366-9ac03b15c040
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WilliamsonShmoys_component_vertex_accounting_vertex_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
import Theorems.Thm_WilliamsonShmoys_component_vertex_accounting_edge_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
import Theorems.Thm_WilliamsonShmoys_component_vertex_accounting_nonempty__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    [Fintype L.ConnectedComponent] :
    (Finset.univ.sum fun c : L.ConnectedComponent =>
      (SimpleGraph.ConnectedComponent.supp c).ncard) = Fintype.card V ∧
    (Finset.univ.sum fun c : L.ConnectedComponent =>
      (L.induce (SimpleGraph.ConnectedComponent.supp c)).edgeSet.ncard) = L.edgeSet.ncard ∧
    (∀ c : L.ConnectedComponent, 1 ≤
      (SimpleGraph.ConnectedComponent.supp c).ncard) := by
  exact ⟨
    WilliamsonShmoys.component_vertex_accounting_vertex_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1 L,
    WilliamsonShmoys.component_vertex_accounting_edge_sum__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1 L,
    WilliamsonShmoys.component_vertex_accounting_nonempty__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1 L⟩
