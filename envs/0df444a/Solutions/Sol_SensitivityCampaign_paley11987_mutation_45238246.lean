-- Prove2me | solution 1 for SensitivityCampaign.paley11987_mutation_45238246
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-27T08:47:02.217161+00:00
-- url     : https://prove2.me/submissions/fb0f46e4-9021-4b7b-8875-10b83882f044

import Definitions.Def_SensitivityCampaign
import Definitions.Def_Paley11987MutationData
import Theorems.Thm_Paley11987Mutation_actualSeeds
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile_achieves_strict_from_seeds
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

set_option autoImplicit false
set_option Elab.async false

namespace Paley11987MutationExponent

namespace LogBounds

theorem logTwoLower :
    (693147180559945309 : ℝ) / 1000000000000000000 ≤ Real.log 2 := by
  have series := Real.sum_range_le_log_div
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at series
  linarith

theorem logTwoUpper :
    Real.log 2 ≤ (693147180559945310 : ℝ) / 1000000000000000000 := by
  have series := Real.log_div_le_sum_range_add
    (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at series
  linarith

theorem log11987Lower :
    (9391578008207099 : ℝ) / 1000000000000000 ≤ Real.log 11987 := by
  have series := Real.sum_range_le_log_div
    (x := (3795 : ℝ) / 20179) (by norm_num) (by norm_num) 15
  have ratio : (1 + (3795 : ℝ) / 20179) / (1 - (3795 : ℝ) / 20179) =
      (11987 : ℝ) / 2 ^ 13 := by
    norm_num
  rw [ratio, Real.log_div (by norm_num) (by positivity), Real.log_pow] at series
  norm_num [Finset.sum_range_succ] at series
  linarith [logTwoLower]

theorem logRadiusUpper :
    Real.log 45238246 ≤ (17627453437461464 : ℝ) / 1000000000000000 := by
  have series := Real.log_div_le_sum_range_add
    (x := (11683814 : ℝ) / 78792678) (by norm_num) (by norm_num) 15
  have ratio : (1 + (11683814 : ℝ) / 78792678) /
      (1 - (11683814 : ℝ) / 78792678) = (45238246 : ℝ) / 2 ^ 25 := by
    norm_num
  rw [ratio, Real.log_div (by norm_num) (by positivity), Real.log_pow] at series
  norm_num [Finset.sum_range_succ] at series
  linarith [logTwoUpper]

end LogBounds

open LogBounds

theorem requestedDecimalBelowEndpoint :
    (2131125302137 : ℝ) / 1000000000000 <
      4 * Real.log 11987 / Real.log 45238246 := by
  have denominatorPositive : 0 < Real.log (45238246 : ℝ) :=
    Real.log_pos (by norm_num)
  apply (lt_div_iff₀ denominatorPositive).2
  nlinarith [log11987Lower, logRadiusUpper]

end Paley11987MutationExponent

-- The top-level declaration exactly matches the campaign goal.
theorem solution :
    SensitivityCampaign.AchievesExponent
      (2131125302137 / 1000000000000 : ℝ) := by
  apply Paley11987Verified.CompactFiniteProfile.achieves_strict_from_seeds
    Paley11987Mutation.initialConstant Paley11987Mutation.radius
    (11987 ^ 4) 16 ((2131125302137 : ℝ) / 1000000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by positivity) ?_ Paley11987Mutation.actualSeeds
  simpa only [Paley11987Mutation.radius, Nat.cast_pow, Nat.cast_ofNat,
    Real.log_pow] using
    Paley11987MutationExponent.requestedDecimalBelowEndpoint
