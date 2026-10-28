-- Prove2me | solution 1 for WilliamsonShmoys.connected_extension_adds_intercomponent_edge
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-28T17:54:09.5136+00:00
-- url     : https://prove2.me/submissions/56c79a1e-5c49-4615-8d46-a4aa57cb9944

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (J M : SimpleGraph V)
    (hJM : J ≤ M)
    (hMConnected : M.Connected)
    (hJNotConnected : ¬ J.Connected) :
    ∃ u v : V, u ≠ v ∧ ¬ J.Adj u v ∧ M.Adj u v := by
  by_contra h
  have hMJ : M ≤ J := by
    intro u v huv
    by_cases hJuv : J.Adj u v
    · exact hJuv
    · have hne : u ≠ v := M.ne_of_adj huv
      exact (h ⟨u, v, hne, hJuv, huv⟩).elim
  have hEq : M = J := le_antisymm hMJ hJM
  exact hJNotConnected (hEq ▸ hMConnected)