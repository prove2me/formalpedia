-- Prove2me | solution 1 for WilliamsonShmoys.component_vertex_accounting_nonempty__p2m_d7ae0e86_02e7_434a_acfe_3fef1dc883ec_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T17:55:42.549917+00:00
-- url     : https://prove2.me/submissions/8d81263e-e6b0-4b92-8358-6e3f514655aa

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (L : SimpleGraph V)
    [Fintype L.ConnectedComponent] :
    ∀ c : L.ConnectedComponent, 1 ≤ (SimpleGraph.ConnectedComponent.supp c).ncard := by
  intro c
  have h : 0 < (SimpleGraph.ConnectedComponent.supp c).ncard :=
    (Set.ncard_pos).mpr (SimpleGraph.ConnectedComponent.nonempty_supp c)
  omega
