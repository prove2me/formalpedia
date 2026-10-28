-- Prove2me | solution 1 for SensitivityCampaign.paley11987_sharper_decimal
-- status  : ACCEPTED   (prove)
-- author  : @rgmohan
-- created : 2026-10-26T17:46:37.410172+00:00
-- url     : https://prove2.me/submissions/44bde30b-eee5-4bf1-bfb1-1ae40305cf92

-- This proof records the sharper decimal consequence of the existing Paley-11987
-- four-phase certificate. It reuses the verified seed construction and proves the
-- only new obligation: the stronger rational decimal remains below its log ratio.
import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile_achieves_strict_from_seeds
import Theorems.Thm_Paley11987Verified_SensitivityCampaign_paley11987_actual_seeds

set_option autoImplicit false
set_option Elab.async false

namespace Paley11987SharperDecimal

namespace CompactFiniteProfile

theorem log_two_lower :
    (693147180559945309 : ℝ) / 1000000000000000000 ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_two_upper :
    Real.log 2 ≤ (693147180559945310 : ℝ) / 1000000000000000000 := by
  have h := Real.log_div_le_sum_range_add (x := (1 : ℝ) / 3) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h
  linarith

end CompactFiniteProfile

namespace ZP

-- These rational bounds avoid trusting floating-point approximations when
-- comparing the campaign decimal with the certificate's logarithmic exponent.
theorem log_11987_lower :
    (9391578008207099 : ℝ) / 1000000000000000 ≤ Real.log 11987 := by
  have h := Real.sum_range_le_log_div
    (x := (3795 : ℝ) / 20179) (by norm_num) (by norm_num) 15
  have hx : (1 + (3795 : ℝ) / 20179) / (1 - (3795 : ℝ) / 20179) =
      (11987 : ℝ) / 2 ^ 13 := by norm_num
  rw [hx, Real.log_div (by norm_num) (by positivity), Real.log_pow] at h
  norm_num [Finset.sum_range_succ] at h
  have ht := CompactFiniteProfile.log_two_lower
  linarith

theorem log_growth_upper :
    Real.log 45238253 ≤ (17627453592197778 : ℝ) / 1000000000000000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (11683821 : ℝ) / 78792685) (by norm_num) (by norm_num) 15
  have hx : (1 + (11683821 : ℝ) / 78792685) /
      (1 - (11683821 : ℝ) / 78792685) = (45238253 : ℝ) / 2 ^ 25 := by norm_num
  rw [hx, Real.log_div (by norm_num) (by positivity), Real.log_pow] at h
  norm_num [Finset.sum_range_succ] at h
  have ht := CompactFiniteProfile.log_two_upper
  linarith

theorem requested_decimal_lt_exponent :
    (2131125283430 : ℝ) / 1000000000000 <
      4 * Real.log 11987 / Real.log 45238253 := by
  have hn := log_11987_lower
  have hr := log_growth_upper
  have hrpos : 0 < Real.log (45238253 : ℝ) := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hrpos).2
  nlinarith

open OAI.Paper320

theorem requested_decimal_of_actual_seeds (hseed : _root_.ZP.ActualSeedStatement) :
    SensitivityCampaign.AchievesExponent
      ((2131125283430 : ℝ) / 1000000000000) := by
  apply _root_.Paley11987Verified.CompactFiniteProfile.achieves_strict_from_seeds
    230508375206254 45238253 (11987 ^ 4) 16
    ((2131125283430 : ℝ) / 1000000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by positivity) ?_ hseed
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_ofNat] using
    requested_decimal_lt_exponent

end ZP

end Paley11987SharperDecimal

-- The top-level name and type exactly match the campaign proposal's goal.
theorem solution :
    SensitivityCampaign.AchievesExponent
      (2131125283430 / 1000000000000 : ℝ) :=
  Paley11987SharperDecimal.ZP.requested_decimal_of_actual_seeds
    Paley11987Verified.SensitivityCampaign.paley11987_actual_seeds
