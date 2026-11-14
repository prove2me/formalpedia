-- Prove2me | solution 1 for avram_chat24_atomic_prefix_interval_core
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:10:44.839942+00:00
-- url     : https://prove2.me/submissions/d64d6c17-f661-4241-ab68-f3737829423e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem solution
    (f : ℝ≥0 → ℝ) (d : ℝ) (B : ℝ≥0)
    (hsum : Summable (fun r : ℝ≥0 =>
      if 0 < r ∧ r ≤ B then Function.leftLim f r - f r else 0))
    (hsource : ∀ t : ℝ≥0, t ≤ B → f t = (t : ℝ) * d -
      ∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0)
    (s t : ℝ≥0) (hst : s ≤ t) (htB : t ≤ B) :
    Summable (fun r : ℝ≥0 =>
      if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) ∧
    (∑' r : ℝ≥0, if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) =
      ((t : ℝ) - (s : ℝ)) * d - (f t - f s) := by
  classical
  have hp (u : ℝ≥0) (hu : u ≤ B) :
      Summable (fun r : ℝ≥0 =>
        if 0 < r ∧ r ≤ u then Function.leftLim f r - f r else 0) := by
    have hfun :
        (fun r : ℝ≥0 =>
          if 0 < r ∧ r ≤ u then Function.leftLim f r - f r else 0) =
        ({r : ℝ≥0 | r ≤ u}).indicator (fun r =>
          if 0 < r ∧ r ≤ B then Function.leftLim f r - f r else 0) := by
      funext r
      by_cases hru : r ≤ u
      · have hrB : r ≤ B := hru.trans hu
        simp [Set.indicator, hru, hrB]
      · simp [Set.indicator, hru]
    rw [hfun]
    exact hsum.indicator _
  have hsB : s ≤ B := hst.trans htB
  have hi : Summable (fun r : ℝ≥0 =>
      if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) := by
    have hfun :
        (fun r : ℝ≥0 =>
          if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) =
        ({r : ℝ≥0 | s < r}).indicator (fun r =>
          if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0) := by
      funext r
      by_cases hsr : s < r
      · have hz : 0 < r := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsr
        simp [Set.indicator, hsr, hz]
      · simp [Set.indicator, hsr]
    rw [hfun]
    exact (hp t htB).indicator _
  have hpoint (r : ℝ≥0) :
      (if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0) =
      (if 0 < r ∧ r ≤ s then Function.leftLim f r - f r else 0) +
      (if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) := by
    by_cases hrs : r ≤ s
    · have hrt : r ≤ t := hrs.trans hst
      simp [hrs, hrt, not_lt_of_ge hrs]
    · have hsr : s < r := lt_of_not_ge hrs
      have hz : 0 < r := lt_of_le_of_lt (show (0 : ℝ≥0) ≤ s from zero_le) hsr
      simp [hrs, hsr, hz]
  have hbalance :
      (∑' r : ℝ≥0, if 0 < r ∧ r ≤ t then Function.leftLim f r - f r else 0) =
      (∑' r : ℝ≥0, if 0 < r ∧ r ≤ s then Function.leftLim f r - f r else 0) +
      (∑' r : ℝ≥0, if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0) := by
    calc
      _ = ∑' r : ℝ≥0,
          ((if 0 < r ∧ r ≤ s then Function.leftLim f r - f r else 0) +
           (if s < r ∧ r ≤ t then Function.leftLim f r - f r else 0)) :=
        tsum_congr hpoint
      _ = _ := (hp s hsB).tsum_add hi
  refine ⟨hi, ?_⟩
  have hs := hsource s hsB
  have ht := hsource t htB
  nlinarith [hbalance]
