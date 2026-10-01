-- Prove2me | solution 1 for VeinottWagnerSS.Bounds.critical_numbers_exist
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:35:47.967378+00:00
-- url     : https://prove2.me/submissions/49b87f8c-0b8b-4b78-aa82-0e0ea0100b1d

import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Instances.Int
import Mathlib.Tactic

open Filter VeinottWagnerSS.Bounds

namespace CVeinott

theorem sublevel_bddBelow (G : ℤ → ℝ)
    (hG_bot : Tendsto G atBot atTop) (c : ℝ) : BddBelow {y : ℤ | G y ≤ c} := by
  obtain ⟨L, hL⟩ := eventually_atBot.mp ((tendsto_atTop.mp hG_bot) (c + 1))
  refine ⟨L, ?_⟩
  intro y hy
  by_contra h
  have := hL y (le_of_lt (lt_of_not_ge h))
  change G y ≤ c at hy
  linarith

theorem int_inf_isLeast (s : Set ℤ) (hs : s.Nonempty) (hb : BddBelow s) :
    IsLeast s (sInf s) :=
  ⟨Int.csInf_mem hs hb, fun _ h => csInf_le hb h⟩

theorem critical (G : ℤ → ℝ) (K α : ℝ) (hα1 : α ≤ 1) (hK : 0 ≤ K)
    (hG_top : Tendsto G atTop atTop) (hG_bot : Tendsto G atBot atTop) :
    IsLeast {y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)} (SHigh G K α) ∧
      IsLeast {y : ℤ | G y ≤ G (SLow G) + K} (sLow G K) ∧
      IsLeast {y : ℤ | G y ≤ G (SLow G) + (1 - α) * K} (sHigh G K α) := by
  constructor
  · apply int_inf_isLeast
    · obtain ⟨N, hN⟩ := eventually_atTop.mp ((tendsto_atTop.mp hG_top) (G (SLow G) + α * K))
      refine ⟨max (SLow G) N, le_max_left _ _, hN _ ?_⟩
      have := le_max_right (SLow G) N
      omega
    · exact ⟨SLow G, fun _ h => h.1⟩
  constructor
  · exact int_inf_isLeast _ ⟨SLow G, by dsimp; linarith⟩
      (sublevel_bddBelow G hG_bot _)
  · exact int_inf_isLeast _ ⟨SLow G, by dsimp; nlinarith⟩
      (sublevel_bddBelow G hG_bot _)

end CVeinott

theorem solution (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) :
    IsLeast {y : ℤ | SLow G ≤ y ∧ G (SLow G) + α * K ≤ G (y + 1)} (SHigh G K α) ∧
      IsLeast {y : ℤ | G y ≤ G (SLow G) + K} (sLow G K) ∧
      IsLeast {y : ℤ | G y ≤ G (SLow G) + (1 - α) * K} (sHigh G K α) :=
  CVeinott.critical G K α hα₁ hK hG_top hG_bot
