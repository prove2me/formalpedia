-- Prove2me | solution 1 for WilliamsonShmoys.planar_edgeFinset_card_mono__p2m_83bb3c80_7c1c_484d_89c0_d393ffbf355c_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T12:25:37.573045+00:00
-- url     : https://prove2.me/submissions/24551746-9e5c-4c7c-ad6b-736a3e1c78cc

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V]
    (H K : SimpleGraph V) [DecidableRel H.Adj] [DecidableRel K.Adj]
    (hHK : ∀ ⦃u v : V⦄, H.Adj u v → K.Adj u v) :
    H.edgeFinset.card ≤ K.edgeFinset.card := by
  exact Finset.card_le_card (SimpleGraph.edgeFinset_mono hHK)