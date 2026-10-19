-- Prove2me | solution 2 for TwoDegenerateGraphs.binomialProbabilityMass_le_mode
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:05.132814+00:00
-- url     : https://prove2.me/submissions/abb87786-255f-44fa-a564-fd225e8aa9b6

import Mathlib
import Definitions.Def_CompactnessAndDegeneracy
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_le_succ_of_lt_mode
import Theorems.Thm_TwoDegenerateGraphs_binomialProbabilityMass_succ_le_of_ge_mode

set_option autoImplicit true
open TwoDegenerateGraphs
open Filter Finset SimpleGraph
open scoped Topology
namespace TwoDegenerateGraphs
theorem _root_.solution
    (trialCount mode successCount : ℕ)
    (hmode : mode ≤ trialCount)
    (hsuccess : successCount ≤ trialCount) :
    binomialProbabilityMass trialCount successCount
        ((mode : ℝ) / (trialCount : ℝ)) ≤
      binomialProbabilityMass trialCount mode
        ((mode : ℝ) / (trialCount : ℝ)) := by
  by_cases htrials : trialCount = 0
  · subst trialCount
    have hmode_zero : mode = 0 := by omega
    have hsuccess_zero : successCount = 0 := by omega
    subst mode
    subst successCount
    exact le_rfl
  by_cases hmode_zero : mode = 0
  · subst mode
    by_cases hsuccess_zero : successCount = 0
    · subst successCount
      exact le_rfl
    · simp [binomialProbabilityMass, hsuccess_zero]
  by_cases hmode_full : mode = trialCount
  · subst mode
    have htrials_real : (trialCount : ℝ) ≠ 0 := by
      exact_mod_cast htrials
    rw [div_self htrials_real]
    by_cases hsuccess_full : successCount = trialCount
    · subst successCount
      exact le_rfl
    · have hpositive : 0 < trialCount - successCount := by omega
      simp [binomialProbabilityMass, hpositive.ne']
  have hmode_lt : mode < trialCount := by omega
  let probability : ℝ := (mode : ℝ) / (trialCount : ℝ)
  have hstep_up (index : ℕ) (hindex : index < mode) :
      binomialProbabilityMass trialCount index probability ≤
        binomialProbabilityMass trialCount (index + 1) probability := by
    exact binomialProbabilityMass_le_succ_of_lt_mode
      trialCount mode index hmode_lt hindex
  have hstep_down (index : ℕ)
      (hindex_mode : mode ≤ index)
      (hindex_trials : index < trialCount) :
      binomialProbabilityMass trialCount (index + 1) probability ≤
        binomialProbabilityMass trialCount index probability := by
    exact binomialProbabilityMass_succ_le_of_ge_mode
      trialCount mode index hmode_lt hindex_mode hindex_trials
  by_cases hbelow : successCount ≤ mode
  · have hwalk (index : ℕ) (hindex : successCount ≤ index) :
        index ≤ mode →
          binomialProbabilityMass trialCount successCount probability ≤
            binomialProbabilityMass trialCount index probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hinduction (by omega)).trans
          (hstep_up index (by omega))
    exact hwalk mode hbelow (le_refl mode)
  · have habove : mode ≤ successCount := by omega
    have hwalk (index : ℕ) (hindex : mode ≤ index) :
        index ≤ trialCount →
          binomialProbabilityMass trialCount index probability ≤
            binomialProbabilityMass trialCount mode probability := by
      induction index, hindex using Nat.le_induction with
      | base =>
        intro _
        exact le_rfl
      | succ index hindex hinduction =>
        intro hupper
        exact (hstep_down index hindex (by omega)).trans
          (hinduction (by omega))
    exact hwalk successCount habove hsuccess
end TwoDegenerateGraphs
