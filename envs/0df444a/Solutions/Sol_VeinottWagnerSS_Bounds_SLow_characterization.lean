-- Prove2me | solution 1 for VeinottWagnerSS.Bounds.SLow_characterization
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T13:39:20.91054+00:00
-- url     : https://prove2.me/submissions/1dea5cf7-2c93-4a66-a9e2-0c3d873ceea1

import Definitions.Def_VeinottWagnerSS_Bounds_CriticalNumbers
import Mathlib.Order.Filter.AtTopBot.Tendsto
import Mathlib.Topology.Instances.Int
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.Data.Int.Interval
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

namespace CVeinott

theorem sublevel_bddAbove (G : ℤ → ℝ)
    (hG_top : Tendsto G atTop atTop) (c : ℝ) : BddAbove {y : ℤ | G y ≤ c} := by
  obtain ⟨U, hU⟩ := eventually_atTop.mp ((tendsto_atTop.mp hG_top) (c + 1))
  refine ⟨U, ?_⟩
  intro y hy
  by_contra h
  have := hU y (le_of_lt (lt_of_not_ge h))
  change G y ≤ c at hy
  linarith

theorem minimizers_nonempty (G : ℤ → ℝ)
    (hG_top : Tendsto G atTop atTop) (hG_bot : Tendsto G atBot atTop) :
    {y : ℤ | ∀ z : ℤ, G y ≤ G z}.Nonempty := by
  have hfin := (sublevel_bddBelow G hG_bot (G 0)).finite_of_bddAbove
    (sublevel_bddAbove G hG_top (G 0))
  obtain ⟨a, ha, hmin⟩ := Set.exists_min_image {y : ℤ | G y ≤ G 0} G hfin ⟨(0 : ℤ), by change G 0 ≤ G 0; exact le_rfl⟩
  refine ⟨a, fun z => ?_⟩
  by_cases hz : G z ≤ G 0
  · exact hmin z hz
  · exact ha.trans (le_of_not_ge hz)

theorem SLow_isLeast (G : ℤ → ℝ)
    (hG_top : Tendsto G atTop atTop) (hG_bot : Tendsto G atBot atTop) :
    IsLeast {y : ℤ | ∀ z : ℤ, G y ≤ G z} (SLow G) := by
  apply int_inf_isLeast _ (minimizers_nonempty G hG_top hG_bot)
  exact (sublevel_bddBelow G hG_bot (G 0)).mono (fun _ hy => hy 0)

theorem SLow_differences (G : ℤ → ℝ)
    (hG_top : Tendsto G atTop atTop) (hG_bot : Tendsto G atBot atTop) :
    G (SLow G) - G (SLow G - 1) < 0 ∧ 0 ≤ G (SLow G + 1) - G (SLow G) := by
  have hmin := SLow_isLeast G hG_top hG_bot
  constructor
  · have hle := hmin.1 (SLow G - 1)
    have hne : G (SLow G) ≠ G (SLow G - 1) := by
      intro heq
      have hp : ∀ z, G (SLow G - 1) ≤ G z := by
        intro z
        rw [← heq]
        exact hmin.1 z
      have := hmin.2 hp
      omega
    exact sub_neg.mpr (lt_of_le_of_ne hle hne)
  · exact sub_nonneg.mpr (hmin.1 _)

theorem SLow_characterization (G : ℤ → ℝ)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Tendsto G atTop atTop) (hG_bot : Tendsto G atBot atTop) :
    IsLeast {y : ℤ | ∀ z : ℤ, G y ≤ G z} (SLow G) ∧
      ∀ y : ℤ, (G y - G (y - 1) < 0 ∧ 0 ≤ G (y + 1) - G y ↔ y = SLow G) := by
  refine ⟨SLow_isLeast G hG_top hG_bot, fun y => ?_⟩
  have hm : Monotone (fun y : ℤ => G (y + 1) - G y) := by
    apply monotone_int_of_le_succ
    intro y
    simpa [add_assoc] using hconv y
  have hS := SLow_differences G hG_top hG_bot
  constructor
  · intro hy
    apply le_antisymm
    · by_contra hn
      have hh := hm (show SLow G ≤ y - 1 by omega)
      simp only [sub_add_cancel] at hh
      linarith [hy.1, hS.2]
    · by_contra hn
      have hh := hm (show y ≤ SLow G - 1 by omega)
      simp only [sub_add_cancel] at hh
      linarith [hy.2, hS.1]
  · rintro rfl
    exact hS

end CVeinott




theorem solution (G : ℤ → ℝ) (K α : ℝ) (hα₀ : 0 ≤ α) (hα₁ : α ≤ 1) (hK : 0 ≤ K)
    (hconv : ∀ y : ℤ, G (y + 1) - G y ≤ G (y + 2) - G (y + 1))
    (hG_top : Filter.Tendsto G Filter.atTop Filter.atTop)
    (hG_bot : Filter.Tendsto G Filter.atBot Filter.atTop) :
    IsLeast {y : ℤ | ∀ z : ℤ, G y ≤ G z} (SLow G) ∧
      ∀ y : ℤ, (G y - G (y - 1) < 0 ∧ 0 ≤ G (y + 1) - G y ↔ y = SLow G) := by
  exact CVeinott.SLow_characterization G hconv hG_top hG_bot
