-- Prove2me | solution 2 for WilliamsonShmoys.exists_minimal_connected_extension__p2m_9960b19b_62d8_4924_9bd4_14f246de67e1_a3
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:11:49.919399+00:00
-- url     : https://prove2.me/submissions/8d35ba11-81ee-4299-bc47-2c148fbf52cb

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V),
      ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
        ∀ u v : V, H.Adj u v → ¬ M.Adj u v →
          ¬ (H.deleteEdges {s(u, v)}).Reachable u v) := by
  intro h
  obtain ⟨H, hMH, hconn, hcritical⟩ :=
    h (V := Empty) (M := (⊤ : SimpleGraph Empty))
  exact isEmptyElim (Classical.choice hconn.nonempty)