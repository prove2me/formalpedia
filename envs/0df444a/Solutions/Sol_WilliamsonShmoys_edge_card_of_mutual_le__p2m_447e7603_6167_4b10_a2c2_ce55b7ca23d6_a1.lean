-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_of_mutual_le__p2m_447e7603_6167_4b10_a2c2_ce55b7ca23d6_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T06:54:52.505757+00:00
-- url     : https://prove2.me/submissions/c482b7e3-6539-466e-bfb1-7a47b36e8327

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M K : SimpleGraph V) (hMK : M ≤ K) (hKM : K ≤ M) :
    (letI : DecidableRel M.Adj := Classical.decRel M.Adj;
     letI : DecidableRel K.Adj := Classical.decRel K.Adj;
     M.edgeFinset.card = K.edgeFinset.card) := by
  have h : M = K := le_antisymm hMK hKM
  cases h
  rfl