-- Prove2me | solution 1 for WilliamsonShmoys.edgeSet_ncard_le_card_sym2__p2m_72a88d75_c4c5_4835_9c9d_bd87f2bf6ce8_a2
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-30T00:34:18.117272+00:00
-- url     : https://prove2.me/submissions/34b06068-3091-427f-8109-6daf019c590d

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) := by
  simpa only [Nat.card_eq_fintype_card] using G.edgeSet.ncard_le_card