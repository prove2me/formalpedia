-- Prove2me | solution 1 for WilliamsonShmoys.triangulated_supergraph_edge_bound__p2m_c3950eb8_41cb_4e65_a38c_065736da1c7d_a5
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:20:15.017284+00:00
-- url     : https://prove2.me/submissions/a465b39e-27ec-4022-9172-e93a3414a2c3

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (H : SimpleGraph V) [DecidableRel H.Adj]
    (hcard : 3 <= Fintype.card V)
    (K : SimpleGraph V) [DecidableRel K.Adj]
    (f : Nat)
    (hsub : ∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v)
    (hle : H.edgeFinset.card ≤ K.edgeFinset.card)
    (heuler : K.edgeFinset.card + 2 = Fintype.card V + f)
    (hfaces : 3 * f = 2 * K.edgeFinset.card) :
    H.edgeFinset.card + 6 ≤ 3 * Fintype.card V := by
  omega