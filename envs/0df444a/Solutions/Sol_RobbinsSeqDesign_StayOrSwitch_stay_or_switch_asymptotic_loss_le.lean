-- Prove2me | solution 1 for RobbinsSeqDesign.StayOrSwitch.stay_or_switch_asymptotic_loss_le
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-06T13:08:51.420224+00:00
-- url     : https://prove2.me/submissions/24b122f7-9a42-4bd2-9e0c-dbc1218ee6a8

import Mathlib
import Definitions.Def_RobbinsSeqDesign_StayOrSwitch_Rules
import Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_expected_average_tendsto
import Theorems.Thm_RobbinsSeqDesign_StayOrSwitch_loss_max

open MeasureTheory ProbabilityTheory Filter Topology
open RobbinsSeqDesign.StayOrSwitch

theorem solution :
    (∀ α β : unitInterval, ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0) → ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1) →
        Tendsto (fun n => expectedAverage ruleR1 α β n) atTop
            (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) ∧
          Tendsto (fun n => max (α : ℝ) β - expectedAverage ruleR1 α β n) atTop
            (𝓝 (delta α β * (1 - delta α β / (1 - gamma α β)))) ∧
          0 ≤ delta α β * (1 - delta α β / (1 - gamma α β)) ∧
          delta α β * (1 - delta α β / (1 - gamma α β)) ≤ 3 - 2 * Real.sqrt 2) ∧
      (∀ α β : unitInterval,
        ((α : ℝ) = 0 ∧ (β : ℝ) = 2 - Real.sqrt 2) ∨ ((α : ℝ) = 2 - Real.sqrt 2 ∧ (β : ℝ) = 0) →
          Tendsto (fun n => max (α : ℝ) β - expectedAverage ruleR1 α β n) atTop
            (𝓝 (3 - 2 * Real.sqrt 2))) := by
  obtain ⟨hmax, hat1, hat2⟩ := loss_max
  have main : ∀ α β : unitInterval, ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0) →
      ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1) →
        Tendsto (fun n => expectedAverage ruleR1 α β n) atTop
            (𝓝 (gamma α β + delta α β ^ 2 / (1 - gamma α β))) ∧
          Tendsto (fun n => max (α : ℝ) β - expectedAverage ruleR1 α β n) atTop
            (𝓝 (delta α β * (1 - delta α β / (1 - gamma α β)))) ∧
          0 ≤ delta α β * (1 - delta α β / (1 - gamma α β)) ∧
          delta α β * (1 - delta α β / (1 - gamma α β)) ≤ 3 - 2 * Real.sqrt 2 := by
    intro α β h0 h1
    have ha1 : (α : ℝ) ≤ 1 := α.2.2
    have hb1 : (β : ℝ) ≤ 1 := β.2.2
    have hlt : (α : ℝ) + β < 2 := by
      by_contra h
      exact h1 ⟨by linarith, by linarith⟩
    have hg : (1 : ℝ) - gamma α β ≠ 0 := by unfold gamma; linarith
    obtain ⟨hE, -⟩ := expected_average_tendsto α β h0 h1
    obtain ⟨hm, hl0, hl1⟩ := hmax α β α.2.1 ha1 β.2.1 hb1 h0 h1
    refine ⟨hE, ?_, hl0, hl1⟩
    have h := hE.const_sub (max (α : ℝ) β)
    convert h using 2
    rw [hm]
    field_simp
    ring
  refine ⟨main, ?_⟩
  have hs1 : Real.sqrt 2 < 2 := by
    rw [show (2 : ℝ) = Real.sqrt 4 by rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  have hs2 : 1 < Real.sqrt 2 := by
    rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  intro α β h
  rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · have h0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0) := fun h ↦ by rw [hb] at h; linarith [h.2]
    have h1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1) := fun h ↦ by rw [ha] at h; linarith [h.1]
    have := (main α β h0 h1).2.1
    rw [ha, hb] at this ⊢
    rwa [hat1] at this
  · have h0 : ¬((α : ℝ) = 0 ∧ (β : ℝ) = 0) := fun h ↦ by rw [ha] at h; linarith [h.1]
    have h1 : ¬((α : ℝ) = 1 ∧ (β : ℝ) = 1) := fun h ↦ by rw [hb] at h; linarith [h.2]
    have := (main α β h0 h1).2.1
    rw [ha, hb] at this ⊢
    rwa [hat2] at this
