-- Prove2me | solution 1 for WilliamsonShmoys.maximal_extension_edge_bound__p2m_d879fe2f_6575_4a1e_b2ae_694852ee5ed8_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T10:28:07.48799+00:00
-- url     : https://prove2.me/submissions/3694b41e-27c4-4c79-837f-5e5f0815ac38

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V] (M N : SimpleGraph V)
    (hMN : M ≤ N) (hNM : N ≤ M)
    (hN : N.edgeSet.ncard + 6 = 3 * Fintype.card V) :
    3 * Fintype.card V ≤ M.edgeSet.ncard + 6 := by
  have hEq : M = N := le_antisymm hMN hNM
  subst M
  omega