-- Prove2me | solution 1 for WilliamsonShmoys.finite_maximal_supergraph_of_subgraph_closed
-- status  : ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-10-26T11:41:17.837664+00:00
-- url     : https://prove2.me/submissions/d4d0f497-e388-42aa-9e42-51eb853315c3

import Mathlib

set_option autoImplicit false

theorem solution
    {V : Type} [Fintype V] [LinearOrder V]
    (P : SimpleGraph V → Prop)
    (hclosed : ∀ ⦃G H : SimpleGraph V⦄, G ≤ H → P H → P G)
    (M : SimpleGraph V) (hM : P M) :
    ∃ Pgraph : SimpleGraph V, M ≤ Pgraph ∧ P Pgraph ∧
      ∀ Q : SimpleGraph V, Pgraph ≤ Q → P Q → Q = Pgraph := by
  classical
  let S : Set (SimpleGraph V) := {G | M ≤ G ∧ P G}
  have hS : S.Nonempty := ⟨M, le_rfl, hM⟩
  obtain ⟨Pgraph, hmax⟩ := S.toFinite.exists_maximal hS
  refine ⟨Pgraph, hmax.1.1, hmax.1.2, ?_⟩
  intro Q hPQ hQ
  have hQS : Q ∈ S := ⟨hmax.1.1.trans hPQ, hQ⟩
  have hQP : Q ≤ Pgraph := hmax.2 hQS hPQ
  exact le_antisymm hQP hPQ