-- Prove2me | solution 1 for SZ.exists_digitB_eq_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T02:53:13.950065+00:00
-- url     : https://prove2.me/submissions/158bbc7b-703f-46cb-99bd-8e136c42e5a3

import Definitions.Def_SZ_DigitParity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Definitions.Def_SZ_CoverGame
import Theorems.Thm_SZ_pick_eq_00
import Theorems.Thm_SZ_pick_eq_20
import Theorems.Thm_SZ_pick_snd_eq_two_iff
import Theorems.Thm_SZ_W_succ
import Theorems.Thm_SZ_W_pos
import Theorems.Thm_SZ_W_ne_three
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
theorem _root_.solution (N : ℕ) : ∃ k, N ≤ k ∧ digitB k = 2 := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ k, N ≤ k → W k < 2 * Real.sqrt 3 := by
    intro k hk
    by_contra h
    exact hcon k hk ((pick_snd_eq_two_iff (W k)).mpr (not_lt.mp h))
  have claim1 : ∀ k, N ≤ k → W k ≤ 1 + Real.sqrt 3 → W k < 2 * Real.sqrt 3 / 3 := by
    intro k hk hle
    have hp : pick (W k) = (0, 0) := pick_eq_00 hle
    have hs : W (k + 1) = 3 * W k := by
      rw [W_succ, digitA, digitB, hp]; push_cast; ring
    have h2 := hlt (k + 1) (by omega)
    rw [hs] at h2
    linarith
  have claim2 : ∀ k, N ≤ k → 1 + Real.sqrt 3 < W k → W k < 2 + 2 * Real.sqrt 3 / 3 := by
    intro k hk hgt
    have hp : pick (W k) = (2, 0) := pick_eq_20 hgt (hlt k hk)
    have hs : W (k + 1) = 3 * W k - 6 := by
      rw [W_succ, digitA, digitB, hp]; push_cast; ring
    have h2 := hlt (k + 1) (by omega)
    rw [hs] at h2
    linarith
  by_cases hex : ∃ j, N ≤ j ∧ 1 + Real.sqrt 3 < W j
  · obtain ⟨j, hjN, hj⟩ := hex
    have habs : ∀ k, j ≤ k → 1 + Real.sqrt 3 < W k ∧ W k < 2 + 2 * Real.sqrt 3 / 3 := by
      intro k hk
      induction k, hk using Nat.le_induction with
      | base => exact ⟨hj, claim2 j hjN hj⟩
      | succ k hk ih =>
        have hkN : N ≤ k := le_trans hjN hk
        have hp : pick (W k) = (2, 0) := pick_eq_20 ih.1 (hlt k hkN)
        have hs : W (k + 1) = 3 * W k - 6 := by
          rw [W_succ, digitA, digitB, hp]; push_cast; ring
        have hgt : 1 + Real.sqrt 3 < W (k + 1) := by
          by_contra hle
          have h3 := claim1 (k + 1) (by omega) (not_lt.mp hle)
          rw [hs] at h3
          linarith [s3_lb, ih.1]
        exact ⟨hgt, claim2 (k + 1) (by omega) hgt⟩
    have hfix : W j = 6 / 2 := by
      refine eq_fixed_of_trapped (c := 6) (D := 1) (K := j) (fun k hk => ?_) (fun k hk => ?_)
      · have hkN : N ≤ k := le_trans hjN hk
        have hp : pick (W k) = (2, 0) := pick_eq_20 (habs k hk).1 (hlt k hkN)
        rw [W_succ, digitA, digitB, hp]; push_cast; ring
      · obtain ⟨ha, hb⟩ := habs k hk
        rw [abs_le]
        constructor <;> linarith [s3_lb, s3_ub]
    exact W_ne_three j (by rw [hfix]; norm_num)
  · push Not at hex
    have hzone : ∀ k, N ≤ k → W k ≤ 1 + Real.sqrt 3 := fun k hk => hex k hk
    have htriple : ∀ n : ℕ, W (N + n) = 3 ^ n * W N := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have hk : N ≤ N + n := Nat.le_add_right _ _
        have hp : pick (W (N + n)) = (0, 0) := pick_eq_00 (hzone _ hk)
        have e : N + (n + 1) = (N + n) + 1 := by omega
        rw [e, W_succ, digitA, digitB, hp]
        push_cast
        rw [ih, pow_succ]
        ring
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((1 + Real.sqrt 3) / W N) (by norm_num : (1:ℝ) < 3)
    have hb := hzone (N + n) (Nat.le_add_right _ _)
    rw [htriple n] at hb
    have hlt2 := (div_lt_iff₀ (W_pos N)).mp hn
    linarith
end SZ
