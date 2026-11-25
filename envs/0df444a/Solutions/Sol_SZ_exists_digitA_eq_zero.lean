-- Prove2me | solution 1 for SZ.exists_digitA_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:46:26.779681+00:00
-- url     : https://prove2.me/submissions/a93ee94e-fec0-4ce6-8770-fc8acce76ca2

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_eq_20
import Theorems.Thm_SZ_pick_eq_22
import Theorems.Thm_SZ_pick_fst_eq_two_iff
import Theorems.Thm_SZ_W_succ
import Theorems.Thm_SZ_digitA_mem
import Theorems.Thm_SZ_W_mem
import Theorems.Thm_SZ_W_ne_three
import Theorems.Thm_SZ_W_ne_top
import Theorems.Thm_SZ_eq_fixed_of_trapped
section
namespace SZ
open Filter Topology
private theorem s3_lb : (1.7 : ℝ) < Real.sqrt 3 :=
  (Real.lt_sqrt (by norm_num)).mpr (by norm_num)
private theorem s3_ub : Real.sqrt 3 < 1.8 := by
  have h : Real.sqrt 3 < Real.sqrt (1.8 ^ 2) := Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
  rwa [Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 1.8)] at h
end SZ
end

set_option autoImplicit false
open SZ
open Filter Topology
namespace SZ
theorem _root_.solution (N : ℕ) : ∃ k, N ≤ k ∧ digitA k = 0 := by
  by_contra hcon
  push Not at hcon
  have htwo : ∀ k, N ≤ k → digitA k = 2 := by
    intro k hk
    rcases digitA_mem k with h | h
    · exact absurd h (hcon k hk)
    · exact h
  have hA : ∀ k, N ≤ k →
      (1 + Real.sqrt 3 < W k ∧ W k < 2 * Real.sqrt 3) ∨ 1 + 3 * Real.sqrt 3 < W k := by
    intro k hk
    exact (pick_fst_eq_two_iff (W k)).mp (htwo k hk)
  by_cases hex : ∃ j, N ≤ j ∧ 1 + Real.sqrt 3 < W j ∧ W j < 2 * Real.sqrt 3
  · obtain ⟨j, hjN, hj1, hj2⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < W k ∧ W k < 2 * Real.sqrt 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj1, hj2⟩
      | succ k hk ih =>
        have hp : pick (W k) = (2, 0) := pick_eq_20 ih.1 ih.2
        have hs : W (k + 1) = 3 * W k - 6 := by
          rw [W_succ, digitA, digitB, hp]; push_cast; ring
        rcases hA (k + 1) (by omega) with h | h
        · exact h
        · exfalso
          rw [hs] at h
          linarith [s3_lb, s3_ub, ih.2]
    have hfix : W j = 6 / 2 := by
      refine eq_fixed_of_trapped (c := 6) (D := 1) (K := j) (fun k hk => ?_) (fun k hk => ?_)
      · have hp : pick (W k) = (2, 0) := pick_eq_20 (habs k hk).1 (habs k hk).2
        rw [W_succ, digitA, digitB, hp]; push_cast; ring
      · obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [s3_lb, s3_ub]
    exact W_ne_three j (by rw [hfix]; norm_num)
  · push Not at hex
    have hA2 : ∀ k, N ≤ k → 1 + 3 * Real.sqrt 3 < W k := by
      intro k hk
      rcases hA k hk with ⟨h1, h2⟩ | h
      · exact absurd h2 (not_lt.mpr (hex k hk h1))
      · exact h
    have hfix : W N = (6 + 6 * Real.sqrt 3) / 2 := by
      refine eq_fixed_of_trapped (c := 6 + 6 * Real.sqrt 3) (D := 2) (K := N)
        (fun k hk => ?_) (fun k hk => ?_)
      · have hp : pick (W k) = (2, 2) := pick_eq_22 (hA2 k hk)
        rw [W_succ, digitA, digitB, hp]; push_cast; ring
      · have h1 := hA2 k hk
        have h2 := (W_mem k).2
        rw [abs_le]
        constructor <;> linarith
    exact W_ne_top N (by rw [hfix]; ring)
end SZ
