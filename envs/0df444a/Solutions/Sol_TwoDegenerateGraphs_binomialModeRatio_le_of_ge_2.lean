-- Prove2me | solution 2 for TwoDegenerateGraphs.binomialModeRatio_le_of_ge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/dbab3f7d-6b82-4199-8784-f9dc5f06acfb

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount mode successCount : ℕ)
    (htrials : 0 < trialCount)
    (hmode : mode ≤ trialCount)
    (hcount : mode ≤ successCount)
    (hsuccess : successCount < trialCount) :
    ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) := by
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub (Nat.le_of_lt hsuccess),
    Nat.cast_sub hmode,
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (successCount : ℝ) - (mode : ℝ) := by
    have hcast : (mode : ℝ) ≤ (successCount : ℝ) := by
      exact_mod_cast hcount
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_le : (mode : ℝ) ≤ (trialCount : ℝ) := by
    exact_mod_cast hmode
  nlinarith
end TwoDegenerateGraphs
