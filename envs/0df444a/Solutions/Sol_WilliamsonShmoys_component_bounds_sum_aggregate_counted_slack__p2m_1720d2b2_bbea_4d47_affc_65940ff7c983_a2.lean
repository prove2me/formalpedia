-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum_aggregate_counted_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a2
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:30:27.776209+00:00
-- url     : https://prove2.me/submissions/cd85865b-4be8-49cf-bb4c-809460991b97

-- ID: c575188a-c998-4798-935c-b2b81c8451d3 | NAME: WilliamsonShmoys.component_bounds_sum_aggregate_counted_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a2 | 未本地编译验证
import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hsum : (∑ s ∈ C, s.card) = Fintype.card V)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hcomponent : ∀ s ∈ C,
      (N.induce (s : Set V)).edgeFinset.card + 3 ≤ 3 * s.card) :
    N.edgeFinset.card + 3 * C.card ≤ 3 * Fintype.card V := by
  have hsumle :
      (∑ s ∈ C, ((N.induce (s : Set V)).edgeFinset.card + 3)) ≤
        ∑ s ∈ C, 3 * s.card :=
    Finset.sum_le_sum (fun s hs => hcomponent s hs)
  have hconst : (∑ s ∈ C, (3 : Nat)) = 3 * C.card := by
    simp [Nat.mul_comm]
  calc
    N.edgeFinset.card + 3 * C.card
        = (∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card) + 3 * C.card := by
            rw [hedges]
    _ = (∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card) + (∑ s ∈ C, (3 : Nat)) := by
            rw [hconst]
    _ = ∑ s ∈ C, ((N.induce (s : Set V)).edgeFinset.card + 3) := by
            rw [Finset.sum_add_distrib]
    _ ≤ ∑ s ∈ C, 3 * s.card := hsumle
    _ = 3 * (∑ s ∈ C, s.card) := by rw [Finset.mul_sum]
    _ = 3 * Fintype.card V := by rw [hsum]
