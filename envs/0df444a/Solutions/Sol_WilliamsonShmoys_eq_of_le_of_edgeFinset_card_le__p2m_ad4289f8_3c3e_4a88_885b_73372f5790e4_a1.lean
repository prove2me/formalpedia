-- Prove2me | solution 1 for WilliamsonShmoys.eq_of_le_of_edgeFinset_card_le__p2m_ad4289f8_3c3e_4a88_885b_73372f5790e4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T07:12:57.123726+00:00
-- url     : https://prove2.me/submissions/d70c1971-dd0b-4be0-943b-facdcff479c1

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (M N : SimpleGraph V) :
    letI : ∀ K : SimpleGraph V, DecidableRel K.Adj :=
      fun K => Classical.decRel K.Adj
    M ≤ N → N.edgeFinset.card ≤ M.edgeFinset.card → N = M := by
  classical
  intro hMN hcard
  apply SimpleGraph.edgeFinset_inj.mp
  exact (Finset.eq_of_subset_of_card_le (SimpleGraph.edgeFinset_mono hMN) hcard).symm