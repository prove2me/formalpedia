-- Prove2me | solution 1 for ShorWiki.continued_fraction_recovers
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T03:37:30.056872+00:00
-- url     : https://prove2.me/submissions/36db7fcf-85b5-43b2-9eae-a6b970fb4f8f

import Mathlib
import Definitions.Def_ShorWiki_Defs
open ShorWiki

theorem solution (j r : ℕ) (hr : 0 < r) (φ : ℝ)
    (h : |(j : ℝ) / r - φ| < 1 / (2 * (r : ℝ) ^ 2)) :
    ∃ m : ℕ, (Real.convergent φ m).num = ((j / Nat.gcd j r : ℕ) : ℤ) ∧
      (Real.convergent φ m).den = r / Nat.gcd j r := by
  set g := Nat.gcd j r with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right _ hr
  set j' := j / g with hj'
  set r' := r / g with hr'
  have hcop : Nat.Coprime j' r' := Nat.coprime_div_gcd_div_gcd hg0
  have hjg : j = j' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_left j r)).symm
  have hrg : r = r' * g := (Nat.div_mul_cancel (Nat.gcd_dvd_right j r)).symm
  have hr'0 : 0 < r' := Nat.div_pos (Nat.gcd_le_right _ hr) hg0
  set q : ℚ := ((j' : ℤ) : ℚ) / ((r' : ℤ) : ℚ) with hq
  have hnum : q.num = j' := by
    rw [hq, Rat.num_div_eq_of_coprime (by exact_mod_cast hr'0) (by simpa using hcop)]
  have hden : (q.den : ℤ) = r' := by
    rw [hq, Rat.den_div_eq_of_coprime (by exact_mod_cast hr'0) (by simpa using hcop)]
  have hden' : q.den = r' := by exact_mod_cast hden
  have hqR : ((q : ℚ) : ℝ) = (j : ℝ) / r := by
    rw [hq]; push_cast
    rw [hjg, hrg]; push_cast
    have : (g : ℝ) ≠ 0 := by exact_mod_cast hg0.ne'
    field_simp
  have hrr : (r' : ℝ) ≤ r := by exact_mod_cast Nat.div_le_self r g
  have hr'R : (0 : ℝ) < r' := by exact_mod_cast hr'0
  have hlt : |φ - (q : ℝ)| < 1 / (2 * (q.den : ℝ) ^ 2) := by
    rw [hqR, abs_sub_comm, hden']
    refine lt_of_lt_of_le h ?_
    apply one_div_le_one_div_of_le (by positivity)
    have := pow_le_pow_left₀ hr'R.le hrr 2
    linarith
  obtain ⟨m, hm⟩ := Real.exists_rat_eq_convergent hlt
  refine ⟨m, ?_, ?_⟩
  · rw [← hm, hnum]
  · rw [← hm, hden']
