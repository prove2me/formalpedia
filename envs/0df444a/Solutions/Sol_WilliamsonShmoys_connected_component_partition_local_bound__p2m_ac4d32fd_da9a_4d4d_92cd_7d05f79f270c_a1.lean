-- Prove2me | solution 1 for WilliamsonShmoys.connected_component_partition_local_bound__p2m_ac4d32fd_da9a_4d4d_92cd_7d05f79f270c_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-11T12:58:23.330076+00:00
-- url     : https://prove2.me/submissions/17dd3618-f930-4e00-8b22-575cca4be7e1

import Mathlib

set_option autoImplicit false

/-- A connected vertex set that is either small or large satisfies the local edge allowance. -/
theorem solution {V : Type} [Fintype V] (H : SimpleGraph V)
    (hBound : ∀ (s : Finset V), (H.induce (↑s : Set V)).Connected →
      3 ≤ Fintype.card {v // v ∈ s} →
      (H.induce (↑s : Set V)).edgeSet.ncard + 6 ≤ 3 * Fintype.card {v // v ∈ s})
    (s : Finset V) (hNonempty : 1 ≤ Fintype.card {v // v ∈ s})
    (hConnected : (H.induce (↑s : Set V)).Connected) :
    (H.induce (↑s : Set V)).edgeSet.ncard +
        (if 3 ≤ Fintype.card {v // v ∈ s} then 6 else 3) ≤
      3 * Fintype.card {v // v ∈ s} := by
  classical
  by_cases h3 : 3 ≤ Fintype.card {v // v ∈ s}
  · rw [if_pos h3]
    exact hBound s hConnected h3
  · rw [if_neg h3]
    have hcard : Fintype.card {v // v ∈ s} = s.card := Fintype.card_coe s
    have hm1 : 1 ≤ s.card := by rw [← hcard]; exact hNonempty
    have hm2 : s.card ≤ 2 := by rw [← hcard]; omega
    have h2 : (H.induce (↑s : Set V)).edgeSet.ncard =
        (H.induce (↑s : Set V)).edgeFinset.card := by
      rw [Set.ncard_eq_toFinset_card']
      rfl
    have h1 : (H.induce (↑s : Set V)).edgeFinset.card ≤ s.card.choose 2 := by
      have := SimpleGraph.card_edgeFinset_le_card_choose_two (G := H.induce (↑s : Set V))
      simpa [hcard] using this
    rw [h2, hcard]
    have hm : s.card = 1 ∨ s.card = 2 := by omega
    rcases hm with hm | hm
    · rw [hm] at h1 ⊢
      norm_num at h1 ⊢
      omega
    · rw [hm] at h1 ⊢
      norm_num at h1 ⊢
      omega
