-- Prove2me | solution 1 for WilliamsonShmoys.edge_ncard_bounded__p2m_465037e3_08d8_4599_8b26_f505e0dc287e_a2
-- status  : ACCEPTED   (prove)
-- author  : @Nihal
-- created : 2026-11-02T19:59:59.256205+00:00
-- url     : https://prove2.me/submissions/35e2bd88-9447-461e-b76a-ed2f4ad37369

import Theorems.Thm_WilliamsonShmoys_edgeSet_ncard_le_card_sym2

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (G : SimpleGraph V) :
    G.edgeSet.ncard ≤ Fintype.card (Sym2 V) :=
  WilliamsonShmoys.edgeSet_ncard_le_card_sym2 G