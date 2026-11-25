-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Lap.rsG_step
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T12:12:41.311124+00:00
-- url     : https://prove2.me/submissions/3cf1098c-31bd-403f-a449-6752d5649780

import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_LowerStepStatement
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_AdjGap
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_Imports
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_InterlacingWalks_RsParLamMinus

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Lap
open ReciprocityTheory.ChartRestriction.DS
namespace ReciprocityTheory.ChartRestriction.DS.Lap
theorem _root_.solution (B : ℕ → ℝ) (h : ℝ) (t j m q N : ℕ) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < N → B q < B (q + 1)) (hBgap : ∀ q, q + 1 < N → h ≤ B (q + 1) - B q)
    (hq : q + 1 < N) :
    rsG B t j m (q + 1) < rsG B t j m q ∧ h ≤ rsG B t j m q - rsG B t j m (q + 1) := by
  have hBq := hBlt q hq
  have hgq := hBgap q hq
  have hmR : (m : ℝ) ≤ (j : ℝ) * t := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e1 : ((q : ℝ) + 1) * t = (q : ℝ) * t + t := by ring
  unfold rsG
  rcases lt_trichotomy (q + 1) j with h1 | h1 | h1
  · rw [if_pos h1, if_pos (show q < j by omega)]
    constructor <;> linarith
  · rw [if_neg (show ¬ q + 1 < j by omega), if_pos h1, if_pos (show q < j by omega)]
    constructor <;> linarith
  · rcases Nat.lt_or_ge j q with h2 | h2
    · rw [if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega),
        if_neg (show ¬ q < j by omega), if_neg (show q ≠ j by omega)]
      push_cast
      have hqt : (0 : ℝ) ≤ (q : ℝ) * t := by positivity
      constructor <;> linarith
    · have hqj : q = j := by omega
      have hqt : (q : ℝ) * t = (j : ℝ) * t := by rw [hqj]
      rw [if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega),
        if_neg (show ¬ q < j by omega), if_pos hqj]
      push_cast
      constructor <;> linarith
end ReciprocityTheory.ChartRestriction.DS.Lap
