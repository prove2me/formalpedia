-- Prove2me | solution 1 for WilliamsonShmoys.strict_simplegraph_supergraph_has_new_edge__p2m_b7a1cfc0_b36e_4034_a5fa_2e691bcea0a4_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T16:49:52.690255+00:00
-- url     : https://prove2.me/submissions/954d16cf-0f2a-4017-ba19-de0ba34e7b5b

import Mathlib

theorem solution
    {V : Type} [Fintype V]
    (K L : SimpleGraph V) (hsub : K ≤ L) (hne : L ≠ K) :
    ∃ u v, L.Adj u v ∧ ¬ K.Adj u v := by
  classical
  by_contra h
  have heq : L = K := by
    ext u v
    constructor
    · intro huv
      by_contra hK
      exact h ⟨u, v, huv, hK⟩
    · intro huv
      exact hsub huv
  exact hne heq