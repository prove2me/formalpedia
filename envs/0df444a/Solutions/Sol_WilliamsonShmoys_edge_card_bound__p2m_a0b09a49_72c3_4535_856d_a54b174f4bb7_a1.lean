-- Prove2me | solution 1 for WilliamsonShmoys.edge_card_bound__p2m_a0b09a49_72c3_4535_856d_a54b174f4bb7_a1
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-11-01T08:16:16.319128+00:00
-- url     : https://prove2.me/submissions/cb131401-496e-4a63-b76c-35d1f4389039

import Mathlib

set_option autoImplicit false

theorem solution {V : Type} [Fintype V] :
    ∃ N : Nat, ∀ (G : SimpleGraph V) [DecidableRel G.Adj], G.edgeFinset.card ≤ N := by
  refine ⟨(Fintype.card V).choose 2, ?_⟩
  intro G
  exact SimpleGraph.card_edgeFinset_le_card_choose_two