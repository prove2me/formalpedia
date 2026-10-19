-- Prove2me | solution 2 for TwoDegenerateGraphs.binomialModeRatio_le_of_lt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/9e52c75b-8659-49a1-a125-1ab884f9b751

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hcount : successCount < mode) :
    ((successCount + 1 : ℕ) : ℝ) *
        (1 - (mode : ℝ) / (trialCount : ℝ)) ≤
      ((trialCount - successCount : ℕ) : ℝ) *
        ((mode : ℝ) / (trialCount : ℝ)) := by
  have htrials : 0 < trialCount := by omega
  have htrials_real : 0 < (trialCount : ℝ) := by
    exact_mod_cast htrials
  have hcomplement :
      1 - (mode : ℝ) / (trialCount : ℝ) =
        ((trialCount - mode : ℕ) : ℝ) / (trialCount : ℝ) := by
    rw [Nat.cast_sub hmode]
    field_simp
  rw [hcomplement, ← mul_div_assoc, ← mul_div_assoc,
    div_le_div_iff_of_pos_right htrials_real,
    Nat.cast_sub hmode,
    Nat.cast_sub (show successCount ≤ trialCount by omega),
    Nat.cast_add, Nat.cast_one]
  have hgap :
      0 ≤ (mode : ℝ) - (successCount : ℝ) - 1 := by
    have hcast : (successCount : ℝ) + 1 ≤ (mode : ℝ) := by
      exact_mod_cast (show successCount + 1 ≤ mode by omega)
    linarith
  have hproduct := mul_nonneg (Nat.cast_nonneg trialCount) hgap
  have hmode_nonneg : 0 ≤ (mode : ℝ) := Nat.cast_nonneg mode
  nlinarith
end TwoDegenerateGraphs
