-- Prove2me | solution 1 for RareDisease.ExogOutcome.reduced_problem
-- status  : ACCEPTED   (prove)
-- author  : @mihalyimark
-- created : 2026-10-18T20:21:34.100967+00:00
-- url     : https://prove2.me/submissions/e99d3220-a29d-4a2f-8f64-727fd70ae3f8

import Mathlib
import Definitions.Def_RareDisease_ExogOutcome_Setting
import Theorems.Thm_RareDisease_ExogOutcome_best_response

open RareDisease.ExogOutcome

/-- (20), p. 15: at the manufacturer's best response the patient welfare is
`p (1 - (1 - β) p)³ / (4 (1 - α) k)` and the government's spending is
`α p² (1 - (1 - β) p)² / (4 (1 - α)² k) + β p² (1 - (1 - β) p)² / (2 (1 - α) k)`. -/
theorem solution (k p α β : ℝ) (hk : 0 < k) (hp0 : 0 < p) (hp1 : p < 1)
    (hpol : RareDisease.Endogenous.IsPolicy α β) (e : ℝ) (he : e ∈ BR k p α β) :
    welfare p β e = p * (1 - (1 - β) * p) ^ 3 / (4 * (1 - α) * k) ∧
    spend k p α β e = α * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (4 * (1 - α) ^ 2 * k)
      + β * p ^ 2 * (1 - (1 - β) * p) ^ 2 / (2 * (1 - α) * k) := by
  have hα1 : α < 1 := hpol.1.2
  -- the singleton best response of (19)
  rw [best_response k p α β hk hp0 hp1 hpol] at he
  simp only [Set.mem_singleton_iff] at he
  rw [he]
  set q := 1 - (1 - β) * p with hqdef
  set d := 2 * (1 - α) * k with hddef
  have h1a : 0 < 1 - α := by linarith [hα1]
  have hdkpos : 0 < 2 * (1 - α) * k := by nlinarith [mul_pos h1a hk]
  have hdne : (2 * (1 - α) * k) ≠ 0 := ne_of_gt hdkpos
  have hd2ne : (2 * (1 - α) * k) ^ 2 ≠ 0 := pow_ne_zero 2 hdne
  have hdk4ne : (4 * (1 - α) ^ 2 * k) ≠ 0 := ne_of_gt (by nlinarith [pow_pos h1a 2, hk])
  constructor
  · show (p * q / d) * q ^ 2 / 2 = p * q ^ 3 / (4 * (1 - α) * k)
    rw [mul_div_assoc, div_mul_div_comm]
    rw [show 4 * (1 - α) * k = d * 2 by ring]
    rw [show p * q * q ^ 2 = p * q ^ 3 by ring]
  · show α * k * (p * q / d) ^ 2 + (p * q / d) * β * p * q
        = α * p ^ 2 * q ^ 2 / (4 * (1 - α) ^ 2 * k) + β * p ^ 2 * q ^ 2 / d
    have s1 : α * k * (p * q / d) ^ 2
        = α * p ^ 2 * q ^ 2 / (4 * (1 - α) ^ 2 * k) := by
      rw [div_pow, ← mul_div_assoc]
      refine (Commute.div_eq_div_iff ?comm hd2ne hdk4ne).mpr ?_
      · show (2 * (1 - α) * k) ^ 2 * (4 * (1 - α) ^ 2 * k)
          = (4 * (1 - α) ^ 2 * k) * (2 * (1 - α) * k) ^ 2
        ring
      · ring
    have s2 : (p * q / d) * β * p * q = β * p ^ 2 * q ^ 2 / d := by
      rw [div_mul_eq_mul_div, div_mul_eq_mul_div, div_mul_eq_mul_div,
        show p * q * β * p * q = β * p ^ 2 * q ^ 2 by ring]
    rw [s1, s2]
