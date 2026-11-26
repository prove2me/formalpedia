-- Prove2me | solution 1 for Sendov.integral_le_tail_gen
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T17:57:49.925554+00:00
-- url     : https://prove2.me/submissions/026c320b-8455-4807-9951-7cc197ee1cfe

import Definitions.Def_Sendov_Common_Quadratic
import Definitions.Def_Sendov_Common_Chord
import Theorems.Thm_Sendov_QQ_le_at_one
import Theorems.Thm_Sendov_QQ_le_chord
import Theorems.Thm_Sendov_QQ_nonneg
import Theorems.Thm_Sendov_continuous_pow_mul_QQ
import Theorems.Thm_Sendov_continuous_rpow_const


set_option autoImplicit false
open Sendov
open MeasureTheory
namespace Sendov
theorem _root_.solution {c A : ℝ} (hfeas : c ^ 2 ≤ A) (hc : 0 < c) (hc1 : c ≤ 1)
    {r : ℝ} (hr : 0 < r) (k : ℕ) :
    (∫ t in (0 : ℝ)..1, t ^ k * QQ c A t ^ r)
      ≤ (∫ t in (0 : ℝ)..1 / c, t ^ k * (1 - c * t) ^ r) + QQ c A 1 ^ r / (k + 1) := by
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hfeas
  set t₀ : ℝ := c / A with ht₀def
  have ht₀pos : 0 < t₀ := by positivity
  set s : ℝ := min t₀ 1 with hsdef
  have hs0 : 0 < s := lt_min ht₀pos one_pos
  have hs1 : s ≤ 1 := min_le_right _ _
  have hcont : Continuous fun u : ℝ => u ^ k * QQ c A u ^ r := continuous_pow_mul_QQ c A k hr.le
  have hint : ∀ a b : ℝ, IntervalIntegrable (fun u : ℝ => u ^ k * QQ c A u ^ r) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hchordcont : Continuous fun u : ℝ => u ^ k * (1 - c * u) ^ r :=
    (by fun_prop : Continuous fun u : ℝ => u ^ k).mul
      ((continuous_rpow_const hr.le).comp (by fun_prop))
  have hsc : s ≤ 1 / c := by
    rcases min_cases t₀ 1 with ⟨h, _⟩ | ⟨h, _⟩
    · rw [hsdef, h, ht₀def, le_div_iff₀ hc, div_mul_eq_mul_div, div_le_one hA]
      nlinarith [hfeas]
    · rw [hsdef, h, le_div_iff₀ hc]
      linarith
  rw [← intervalIntegral.integral_add_adjacent_intervals (hint 0 s) (hint s 1)]
  have hfirst : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
      ≤ ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r := by
    have hle : (∫ u in (0 : ℝ)..s, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_mono_on hs0.le (hint 0 s)
        (hchordcont.intervalIntegrable _ _) ?_
      intro u hu
      obtain ⟨hu0, hus⟩ := hu
      have huv : A * u ≤ c := by
        have hut : u ≤ t₀ := le_trans hus (min_le_left _ _)
        rw [ht₀def, le_div_iff₀ hA] at hut
        linarith
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (QQ_nonneg hfeas u) (QQ_le_chord hu0 huv) hr.le) (pow_nonneg hu0 k)
    refine hle.trans ?_
    have hrest : 0 ≤ ∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r := by
      refine intervalIntegral.integral_nonneg hsc ?_
      intro u hu
      have : 0 ≤ 1 - c * u := by
        have := hu.2
        rw [le_div_iff₀ hc] at this
        linarith
      exact mul_nonneg (pow_nonneg (le_trans hs0.le hu.1) k) (Real.rpow_nonneg this _)
    have hadd : (∫ u in (0 : ℝ)..s, u ^ k * (1 - c * u) ^ r)
        + (∫ u in s..1 / c, u ^ k * (1 - c * u) ^ r)
        = ∫ u in (0 : ℝ)..1 / c, u ^ k * (1 - c * u) ^ r :=
      intervalIntegral.integral_add_adjacent_intervals
        (hchordcont.intervalIntegrable 0 s) (hchordcont.intervalIntegrable s (1 / c))
    linarith
  have hsecond : (∫ u in s..1, u ^ k * QQ c A u ^ r) ≤ QQ c A 1 ^ r / (k + 1) := by
    have hBnn : (0 : ℝ) ≤ QQ c A 1 ^ r := Real.rpow_nonneg (QQ_nonneg hfeas 1) _
    have hQB : ∀ u ∈ Set.Icc s 1, QQ c A u ≤ QQ c A 1 := by
      intro u hu
      rcases le_or_gt t₀ u with h | h
      · rw [ht₀def, div_le_iff₀ hA] at h
        exact QQ_le_at_one hA.le (by linarith) hu.2
      · have hu1 : u = 1 := by
          rcases min_cases t₀ 1 with ⟨he, _⟩ | ⟨he, _⟩
          · rw [hsdef, he] at hu; linarith [hu.1]
          · rw [hsdef, he] at hu; linarith [hu.1, hu.2]
        rw [hu1]
    have hle : (∫ u in s..1, u ^ k * QQ c A u ^ r)
        ≤ ∫ u in s..1, QQ c A 1 ^ r * u ^ k := by
      refine intervalIntegral.integral_mono_on hs1 (hint s 1)
        ((by fun_prop : Continuous fun u : ℝ => QQ c A 1 ^ r * u ^ k).intervalIntegrable _ _) ?_
      intro u hu
      have := Real.rpow_le_rpow (QQ_nonneg hfeas u) (hQB u hu) hr.le
      nlinarith [pow_nonneg (le_trans hs0.le hu.1) k, this, hBnn]
    refine hle.trans ?_
    rw [intervalIntegral.integral_const_mul, integral_pow]
    have hsk : (0 : ℝ) ≤ s ^ (k + 1) := pow_nonneg hs0.le _
    rw [one_pow, ← mul_div_assoc]
    gcongr
    nlinarith [mul_nonneg hBnn hsk]
  linarith
end Sendov
