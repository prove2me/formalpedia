-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum_aggregate_parts__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : ACCEPTED   (prove)
-- author  : @dphz
-- created : 2026-11-05T14:31:03.314917+00:00
-- url     : https://prove2.me/submissions/d41eef45-a829-47a8-a1ce-bc7683169875

-- ID: 07d89f15-0bc5-48be-8d85-07edd32a1069 | NAME: WilliamsonShmoys.component_bounds_sum_aggregate_parts__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1 | 未本地编译验证
import Mathlib
set_option autoImplicit false

theorem solution {V : Type} [Fintype V] [LinearOrder V]
    (N : SimpleGraph V) (dN : DecidableRel N.Adj)
    (C : Finset (Finset V))
    (hcard : 3 <= Fintype.card V)
    (hmany : 2 <= C.card)
    (hsum : (∑ s ∈ C, s.card) = Fintype.card V)
    (hedges : N.edgeFinset.card = ∑ s ∈ C, (N.induce (s : Set V)).edgeFinset.card)
    (hcomponent : ∀ s ∈ C,
      (N.induce (s : Set V)).edgeFinset.card + 3 <= 3 * s.card) :
    N.edgeFinset.card <= 3 * Fintype.card V - 6 := by
  have hagg : N.edgeFinset.card + 3 * C.card ≤ 3 * Fintype.card V := by
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
  omega
