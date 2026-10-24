-- Prove2me | solution 1 for SensitivityCampaign.paley11987_four_phase
-- status  : ACCEPTED   (prove)
-- author  : @yousofy
-- created : 2026-10-23T05:59:35.107873+00:00
-- url     : https://prove2.me/submissions/de91c83c-2076-430d-98ac-0ed12f876008

import Definitions.Def_SensitivityCampaign
import Definitions.Def_SensitivitySeparation
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.GroupWithZero.Units.Equiv
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.GroupWithZero.Basic
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Combinatorics.Digraph.Basic
import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Union
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.JacobiSum.Basic
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Tauto
import Definitions.Def_Paley11987Support_036
import Definitions.Def_Paley11987Support_055
import Theorems.Thm_Paley11987Verified_CompactFiniteProfile_achieves_strict_from_seeds
import Theorems.Thm_Paley11987Verified_SensitivityCampaign_paley11987_actual_seeds

set_option autoImplicit false
set_option Elab.async false
section z83

namespace CompactFiniteProfile

theorem log_two_lower :
    (693147180559945309 : ℝ) / 1000000000000000000 ≤ Real.log 2 := by
  have h := Real.sum_range_le_log_div (x := (1 : ℝ)/3) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h
  linarith

theorem log_two_upper :
    Real.log 2 ≤ (693147180559945310 : ℝ) / 1000000000000000000 := by
  have h := Real.log_div_le_sum_range_add (x := (1 : ℝ)/3) (by norm_num) (by norm_num) 20
  norm_num [Finset.sum_range_succ] at h
  linarith

end CompactFiniteProfile
end z83

section z84

namespace ZP

theorem log_11987_lower :
    (9391578008207099 : ℝ) / 1000000000000000 ≤ Real.log 11987 := by
  have h := Real.sum_range_le_log_div
    (x := (3795 : ℝ)/20179) (by norm_num) (by norm_num) 15
  have hx : (1 + (3795 : ℝ)/20179) / (1 - (3795 : ℝ)/20179) =
      (11987 : ℝ) / 2^13 := by norm_num
  rw [hx, Real.log_div (by norm_num) (by positivity), Real.log_pow] at h
  norm_num [Finset.sum_range_succ] at h
  have ht := CompactFiniteProfile.log_two_lower
  linarith

theorem log_growth_upper :
    Real.log 45238253 ≤ (17627453592197778 : ℝ) / 1000000000000000 := by
  have h := Real.log_div_le_sum_range_add
    (x := (11683821 : ℝ)/78792685) (by norm_num) (by norm_num) 15
  have hx : (1 + (11683821 : ℝ)/78792685) /
      (1 - (11683821 : ℝ)/78792685) = (45238253 : ℝ) / 2^25 := by norm_num
  rw [hx, Real.log_div (by norm_num) (by positivity), Real.log_pow] at h
  norm_num [Finset.sum_range_succ] at h
  have ht := CompactFiniteProfile.log_two_upper
  linarith

theorem requested_decimal_lt_exponent :
    (2131121719190 : ℝ) / 1000000000000 <
      4 * Real.log 11987 / Real.log 45238253 := by
  have hn := log_11987_lower
  have hr := log_growth_upper
  have hrpos : 0 < Real.log (45238253 : ℝ) := Real.log_pos (by norm_num)
  apply (lt_div_iff₀ hrpos).2
  nlinarith



end ZP
end z84

section z85

namespace ZP
open OAI.Paper320





theorem requested_decimal_of_actual_seeds (hseed : ActualSeedStatement) :
    SensitivityCampaign.AchievesExponent ((2131121719190 : ℝ) / 1000000000000) := by
  apply _root_.Paley11987Verified.CompactFiniteProfile.achieves_strict_from_seeds
    230508375206254 45238253 (11987^4) 16
    ((2131121719190 : ℝ) / 1000000000000)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by positivity) ?_ hseed
  simpa only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_ofNat] using
    requested_decimal_lt_exponent

end ZP
end z85

section z234

noncomputable section

namespace SensitivityCampaign
open OAI.Paper320 ZT ZP





theorem reach_paley11987_requested_decimal :
    AchievesExponent ((2131121719190 : ℝ)/1000000000000) :=
  ZP.requested_decimal_of_actual_seeds _root_.Paley11987Verified.SensitivityCampaign.paley11987_actual_seeds



end SensitivityCampaign

theorem _root_.solution :
    SensitivityCampaign.AchievesExponent ((2131121719190 : ℝ)/1000000000000) :=
  SensitivityCampaign.reach_paley11987_requested_decimal
end
end z234
