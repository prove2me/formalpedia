-- Prove2me | solution 1 for ScheduledQueue.Stability.beta2_bounded
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-24T21:49:37.48936+00:00
-- url     : https://prove2.me/submissions/4fe963dc-902b-48fe-ae1d-337fc02cd2e2

import Mathlib
import Definitions.Def_ScheduledQueue_Stability_Setting
import Definitions.Def_ScheduledQueue_Stability_Reversed

open MeasureTheory ProbabilityTheory Set Filter Topology ENNReal

open ScheduledQueue.Stability in
theorem solution {Ω : Type*} (h : ℝ) (hh : 0 < h) (ξ : ℤ → Ω → ℝ) (U : Ω → ℝ) :
    ∀ (ω : Ω) (c : ℝ), 0 ≤ c → (∀ j, ξ j ω ≤ c) → U ω ∈ Icc (0 : ℝ) 1 →
      ∀ s : ℝ, 0 ≤ s → beta2 h ξ U s ω ≤ ((⌊c / h⌋₊ + 1 : ℕ) : ℕ∞) := by
  intro ω c hc hξ hU s hs
  set k : ℕ := ⌊s / h⌋₊
  set m : ℕ := ⌊c / h⌋₊
  have hk : s / h < k + 1 := Nat.lt_floor_add_one _
  have hm : c / h < m + 1 := Nat.lt_floor_add_one _
  have hsub : {j : ℤ | (k : ℤ) + 1 ≤ j ∧ revArrival h ξ U j ω ∈ Ioc 0 s} ⊆
      (Finset.Icc ((k : ℤ) + 1) ((k : ℤ) + m + 1) : Set ℤ) := by
    intro j ⟨hj1, hj2⟩
    simp only [Finset.coe_Icc, mem_Icc]
    refine ⟨hj1, ?_⟩
    have h2 := hj2.2
    simp only [revArrival] at h2
    have hξj := hξ j
    have hjle : (j : ℝ) * h ≤ s + c := by nlinarith [hU.1]
    have hjlt : (j : ℝ) < k + 1 + (m + 1) := by
      have : (j : ℝ) ≤ s / h + c / h := by
        rw [← add_div, le_div_iff₀ hh]; linarith
      linarith
    have : j < (k : ℤ) + 1 + (m + 1) := by exact_mod_cast hjlt
    omega
  calc beta2 h ξ U s ω ≤ _ := encard_le_encard hsub
    _ = _ := by
        rw [Set.encard_coe_eq_coe_finsetCard, Int.card_Icc]
        congr 1
        omega
