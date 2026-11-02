-- Prove2me | solution 1 for avram_wave6_monotone_ennreal_diagonal_nat_clip_sup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:49.18471+00:00
-- url     : https://prove2.me/submissions/07dfed85-40fa-46fa-ac12-0a8db5510703

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
noncomputable section

theorem solution
    (a : ℕ → ℝ≥0∞) (ha : Monotone a) :
    (⨆ n : ℕ, min (a n) (n : ℝ≥0∞)) = (⨆ n : ℕ, a n) := by
  apply le_antisymm
  · refine iSup_le fun n => ?_
    exact (min_le_left (a n) (n : ℝ≥0∞)).trans (le_iSup a n)
  · calc
      (⨆ n : ℕ, a n) =
          min (⨆ n : ℕ, a n) (⨆ m : ℕ, (m : ℝ≥0∞)) := by
            simp [ENNReal.iSup_natCast]
      _ = (⨆ n : ℕ, ⨆ m : ℕ, min (a n) (m : ℝ≥0∞)) := by
            rw [iSup_inf_eq]
            simp_rw [inf_iSup_eq]
      _ ≤ (⨆ k : ℕ, min (a k) (k : ℝ≥0∞)) := by
            refine iSup_le fun n => ?_
            refine iSup_le fun m => ?_
            let k : ℕ := max n m
            have han : a n ≤ a k := ha (Nat.le_max_left n m)
            have hkm : (m : ℝ≥0∞) ≤ (k : ℝ≥0∞) := by
              exact_mod_cast Nat.le_max_right n m
            exact (min_le_min han hkm).trans
              (le_iSup (fun j : ℕ => min (a j) (j : ℝ≥0∞)) k)
