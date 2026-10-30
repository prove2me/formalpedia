-- Prove2me | solution 1 for WilliamsonShmoys.exists_minimal_connected_supergraph__p2m_af495ada_8c1f_484d_a693_c45034ff536b_a2
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:09:13.418798+00:00
-- url     : https://prove2.me/submissions/681f4126-8a91-4251-bfdf-49c6e156de6d

import Mathlib

set_option autoImplicit false

open SimpleGraph

theorem solution :
    ¬ (∀ {V : Type} [Fintype V] [LinearOrder V] (M : SimpleGraph V),
      ∃ H : SimpleGraph V, M ≤ H ∧ H.Connected ∧
        ∀ K : SimpleGraph V, M ≤ K → K ≤ H → K.Connected → K = H) := by
  intro h
  obtain ⟨H, hMH, hconn, hminimal⟩ := h (V := Empty) (⊥ : SimpleGraph Empty)
  exact isEmptyElim (Classical.choice hconn.nonempty)