-- Prove2me | solution 1 for Real.tendsto_atTop_of_add_le_step
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-11-14T20:36:37.568657+00:00
-- url     : https://prove2.me/submissions/506ee099-9c2c-438d-b2b3-61e4290378ad

import Mathlib

open Filter Topology

namespace RH8

/-- A continuous `m : ℝ → ℝ` that gains at least `1` over every step of length `L > 0` beyond
`s₀` tends to `+∞`. -/
theorem tendsto_atTop_of_add_le_step_aux (m : ℝ → ℝ) (hm : Continuous m) (L s₀ : ℝ)
    (hL : 0 < L) (hstep : ∀ s, s₀ ≤ s → m s + 1 ≤ m (s + L)) : Tendsto m atTop atTop := by
  have hind : ∀ j : ℕ, ∀ t, s₀ ≤ t → m t + j ≤ m (t + j * L) := by
    intro j
    induction j with
    | zero => intro t _; simp
    | succ j ih =>
      intro t ht
      have h1 := ih t ht
      have h2 := hstep (t + j * L) (by nlinarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)])
      push_cast
      have : t + (j + 1) * L = t + j * L + L := by ring
      rw [this]
      linarith
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := s₀) (b := s₀ + L)).bddBelow_image hm.continuousOn
  rw [tendsto_atTop_atTop]
  intro b
  obtain ⟨j₀, hj₀⟩ := exists_nat_ge (b - B)
  refine ⟨s₀ + (j₀ + 1) * L, fun s hs => ?_⟩
  set j : ℕ := ⌊(s - s₀) / L⌋₊ with hj
  have hq : 0 ≤ (s - s₀) / L := div_nonneg (by nlinarith) hL.le
  have hjle : (j : ℝ) ≤ (s - s₀) / L := Nat.floor_le hq
  have hjlt : (s - s₀) / L < j + 1 := Nat.lt_floor_add_one _
  have hjL : (j : ℝ) * L ≤ s - s₀ := by rwa [le_div_iff₀ hL] at hjle
  have hjL' : s - s₀ < (j + 1) * L := by rwa [div_lt_iff₀ hL] at hjlt
  have hj0 : (j₀ : ℝ) ≤ j := by
    have : (j₀ + 1 : ℝ) * L ≤ s - s₀ := by linarith
    have h3 : (j₀ : ℝ) + 1 < j + 1 + 1 := by
      by_contra hc
      push_neg at hc
      nlinarith
    have h4 : (j₀ : ℕ) < j + 1 := by exact_mod_cast (by linarith : (j₀ : ℝ) < j + 1)
    exact_mod_cast Nat.lt_succ_iff.1 h4
  set t := s - j * L with ht
  have htI : t ∈ Set.Icc s₀ (s₀ + L) := ⟨by linarith, by linarith⟩
  have hmt : B ≤ m t := hB ⟨t, htI, rfl⟩
  have := hind j t htI.1
  have hs' : t + j * L = s := by rw [ht]; ring
  rw [hs'] at this
  linarith

end RH8

open Real

open Filter Topology

theorem solution (m : ℝ → ℝ) (hm : Continuous m) (L s₀ : ℝ)
    (hL : 0 < L) (hstep : ∀ s, s₀ ≤ s → m s + 1 ≤ m (s + L)) : Tendsto m atTop atTop :=
  RH8.tendsto_atTop_of_add_le_step_aux m hm L s₀ hL hstep
