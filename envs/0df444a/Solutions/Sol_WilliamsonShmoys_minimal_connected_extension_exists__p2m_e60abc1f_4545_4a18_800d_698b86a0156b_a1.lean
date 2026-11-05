-- Prove2me | solution 1 for WilliamsonShmoys.minimal_connected_extension_exists__p2m_e60abc1f_4545_4a18_800d_698b86a0156b_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-04T18:41:45.84472+00:00
-- url     : https://prove2.me/submissions/da19ec70-2924-4a2e-accc-195bfcf2afd1

import Mathlib

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false

open SimpleGraph

theorem solution
    {V : Type} [Fintype V] [LinearOrder V] [Nonempty V]
    (M : SimpleGraph V) :
    ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
      ∀ K : SimpleGraph V, M ≤ K → K ≤ H → K.Connected → H ≤ K := by
  classical
  let p : SimpleGraph V → Prop := fun H => M ≤ H ∧ H.Connected
  have htopconn : (⊤ : SimpleGraph V).Connected := by
    change (SimpleGraph.completeGraph V).Connected
    exact SimpleGraph.connected_top
  have hp_top : p ⊤ := ⟨le_top, htopconn⟩
  obtain ⟨H, _hHle, hHmin⟩ :=
    (Set.toFinite {H : SimpleGraph V | p H}).exists_le_minimal hp_top
  refine ⟨H, hHmin.1.1, hHmin.1.2, ?_⟩
  intro K hMK hKH hKc
  exact hHmin.2 ⟨hMK, hKc⟩ hKH
