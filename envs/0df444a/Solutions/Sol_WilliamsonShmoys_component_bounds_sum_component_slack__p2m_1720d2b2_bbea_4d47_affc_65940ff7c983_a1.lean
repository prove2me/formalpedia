-- Prove2me | solution 1 for WilliamsonShmoys.component_bounds_sum_component_slack__p2m_1720d2b2_bbea_4d47_affc_65940ff7c983_a1
-- status  : ACCEPTED   (prove)
-- author  : @ducloc
-- created : 2026-11-10T17:43:29.452718+00:00
-- url     : https://prove2.me/submissions/1ec7b5aa-6669-4b9c-af61-89c829aaadbd

import Mathlib

open scoped BigOperators

set_option autoImplicit false

/-- Each connected block of at most two vertices satisfies the slack inequality `e + 3 ≤ 3v`, and
for larger blocks it follows from the `3v - 6` edge bound. -/
theorem solution {V : Type*} [Fintype V] [LinearOrder V] (N : SimpleGraph V)
    (dN : DecidableRel N.Adj) (C : Finset (Finset V)) (hnonempty : ∀ s ∈ C, s.Nonempty)
    (hconnected : ∀ s ∈ C, (N.induce (s : Set V)).Connected)
    (hlocal : ∀ s : Finset V, 3 <= s.card →
      (N.induce (s : Set V)).Connected →
      (N.induce (s : Set V)).edgeFinset.card <= 3 * s.card - 6) :
    ∀ s ∈ C, (N.induce (s : Set V)).edgeFinset.card + 3 <= 3 * s.card := by
  classical
  intro s hs
  have hconn := hconnected s hs
  rcases lt_or_ge s.card 3 with hsmall | hbig
  · have hne := hnonempty s hs
    have hpos : 0 < s.card := Finset.card_pos.mpr hne
    have hle : (N.induce (s : Set V)).edgeFinset.card ≤ s.card.choose 2 := by
      have h := SimpleGraph.card_edgeFinset_le_card_choose_two (G := N.induce (s : Set V))
      simpa using h
    have h1 : s.card = 1 ∨ s.card = 2 := by omega
    rcases h1 with h1 | h1
    · rw [h1] at hle ⊢
      have hc : (1 : ℕ).choose 2 = 0 := Nat.choose_eq_zero_of_lt (by norm_num)
      rw [hc] at hle
      have h31 : 3 * 1 = 3 := by norm_num
      rw [h31]
      omega
    · rw [h1] at hle ⊢
      have hc : (2 : ℕ).choose 2 = 1 := by decide
      rw [hc] at hle
      have h32 : 3 * 2 = 6 := by norm_num
      rw [h32]
      omega
  · have h := hlocal s hbig hconn
    omega
