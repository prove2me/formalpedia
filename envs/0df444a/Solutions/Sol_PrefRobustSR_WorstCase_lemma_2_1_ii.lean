-- Prove2me | solution 1 for PrefRobustSR.WorstCase.lemma_2_1_ii
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T15:21:27.435481+00:00
-- url     : https://prove2.me/submissions/039f2cd7-820e-4019-9cbe-c0f4d1dde8cf

import Mathlib
import Definitions.Def_PrefRobustSR_WorstCase_Model

set_option autoImplicit false
open MeasureTheory PrefRobustSR.WorstCase
open scoped ENNReal

namespace PRH

lemma tendsto_loss (l : ℝ → ℝ) (hl : l ∈ LossClass) : Filter.Tendsto l Filter.atTop Filter.atTop := by
  obtain ⟨hc, hm, z0, hz0, hs⟩ := hl
  have hs0 : 0 < l 1 - l 0 := by
    have : l 0 < l 1 := hs (show (0:ℝ) ∈ Set.Ici z0 from hz0.le) (show (1:ℝ) ∈ Set.Ici z0 from by
      simp only [Set.mem_Ici]; linarith) (by norm_num)
    linarith
  have key : ∀ x : ℝ, 1 < x → l 1 + (l 1 - l 0) * (x - 1) ≤ l x := by
    intro x hx
    have := hc.slope_mono_adjacent (x := 0) (y := 1) (z := x) (Set.mem_univ _) (Set.mem_univ _)
      (by norm_num) hx
    have hx' : 0 < x - 1 := by linarith
    simp only [sub_zero, div_one] at this
    rw [le_div_iff₀ hx'] at this
    linarith
  rw [Filter.tendsto_atTop]
  intro b
  rw [Filter.eventually_atTop]
  refine ⟨max 2 (1 + (b - l 1) / (l 1 - l 0)), fun x hx => ?_⟩
  have h1 : 1 < x := by have := le_max_left 2 (1 + (b - l 1) / (l 1 - l 0)); linarith
  have h2 : (b - l 1) / (l 1 - l 0) ≤ x - 1 := by
    have := le_max_right 2 (1 + (b - l 1) / (l 1 - l 0)); linarith
  rw [div_le_iff₀ hs0] at h2
  have := key x h1
  nlinarith

end PRH

theorem solution (l : ℝ → ℝ) (hl : l ∈ LossClass) :
    Filter.Tendsto l Filter.atTop Filter.atTop := PRH.tendsto_loss l hl

