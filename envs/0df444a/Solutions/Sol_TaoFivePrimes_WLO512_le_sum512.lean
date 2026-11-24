-- Prove2me | solution 1 for TaoFivePrimes.WLO512_le_sum512
-- status  : ACCEPTED   (prove)
-- author  : @andreaskapfer
-- created : 2026-09-29T12:57:47.028396+00:00
-- url     : https://prove2.me/submissions/0d8f8ad7-b0c2-4604-b184-28729b26dd09

import Mathlib
import Definitions.Def_TaoFivePrimes_mertens_cert_511_tables

open Finset
set_option maxRecDepth 1000000
set_option maxHeartbeats 16000000
set_option linter.unusedVariables false

namespace TaoFivePrimes

private lemma primesLE_succ (k : Nat) :
    Nat.primesLE (k+1) = if (k+1).Prime then insert (k+1) (Nat.primesLE k) else Nat.primesLE k := by
  ext p
  rw [Nat.mem_primesLE]
  by_cases h : (k+1).Prime
  · rw [if_pos h, Finset.mem_insert, Nat.mem_primesLE]
    constructor
    · intro hp
      rcases eq_or_lt_of_le hp.1 with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨by omega, hp.2⟩
    · rintro (rfl | ⟨hle, hpr⟩)
      · exact ⟨le_refl _, h⟩
      · exact ⟨by omega, hpr⟩
  · rw [if_neg h, Nat.mem_primesLE]
    constructor
    · intro hp
      have hne : p ≠ k+1 := fun he => h (he ▸ hp.2)
      exact ⟨by omega, hp.2⟩
    · intro hp; exact ⟨by omega, hp.2⟩


private lemma sum_primesLE_succ {α : Type*} [AddCommMonoid α] (k : Nat) (f : Nat → α) :
    ∑ p ∈ Nat.primesLE (k+1), f p = ∑ p ∈ Nat.primesLE k, f p + if (k+1).Prime then f (k+1) else 0 := by
  rw [primesLE_succ k]
  by_cases h : (k+1).Prime
  · rw [if_pos h, if_pos h, Finset.sum_insert]
    · rw [add_comm]
    · simp only [Nat.mem_primesLE]; omega
  · rw [if_neg h, if_neg h, add_zero]


private lemma log_sub_ge_series (p : Nat) (hp : 2 ≤ p) :
    1/(p:Real) - (∑ i ∈ Finset.range 16, (1/(p:Real))^(i+1)/(i+1)) - 2*(1/(p:Real))^17 ≤
      Real.log (1 - 1/(p:Real)) + 1/(p:Real) := by
  have hp2 : (2:Real) ≤ (p:Real) := by exact_mod_cast hp
  have hx0 : (0:Real) < 1/(p:Real) := by positivity
  have hxle : (1:Real)/(p:Real) ≤ 1/2 := one_div_le_one_div_of_le (by norm_num) hp2
  have h := Real.abs_log_sub_add_sum_range_le (x := 1/(p:Real)) (by rw [abs_of_pos hx0]; linarith) 16
  obtain ⟨hlow, -⟩ := abs_le.mp h
  have herr : |1/(p:Real)|^(16+1)/(1 - |1/(p:Real)|) ≤ 2*(1/(p:Real))^17 := by
    rw [abs_of_pos hx0]
    have hpos : (0:Real) < 1 - 1/(p:Real) := by linarith
    rw [div_le_iff₀ hpos]
    have hone : (1:Real) ≤ 2 * (1 - 1/(p:Real)) := by linarith
    calc (1/(p:Real))^(16+1) = (1/(p:Real))^(16+1) * 1 := by ring
      _ ≤ (1/(p:Real))^(16+1) * (2*(1 - 1/(p:Real))) :=
            mul_le_mul_of_nonneg_left hone (by positivity)
      _ = 2*(1/(p:Real))^17*(1 - 1/(p:Real)) := by
            rw [show 16 + 1 = 17 by norm_num]; ring
  linarith [le_trans (neg_le_neg herr) hlow]


private lemma mem_pl521_of_mem_primesLE (p : Nat) (hp : p ∈ Nat.primesLE 521) : p ∈ pl521 := by
  have hle : p ≤ 521 := (Nat.mem_primesLE.mp hp).1
  have h2 : 2 ≤ p := (Nat.mem_primesLE.mp hp).2.two_le
  interval_cases p <;> (first | decide | (exact absurd (Nat.mem_primesLE.mp hp).2 (by norm_num)))


end TaoFivePrimes

open TaoFivePrimes

private lemma wlo_le_w_of_mem (p : Nat) (hp : p ∈ Nat.primesLE 512) :
    (wlo p : Real) ≤ Real.log (1 - 1/(p:Real)) + 1/(p:Real) := by
  have hle : p ≤ 512 := (Nat.mem_primesLE.mp hp).1
  have hpr : p.Prime := (Nat.mem_primesLE.mp hp).2
  have hp521 : p ∈ Nat.primesLE 521 := by
    rw [Nat.mem_primesLE]
    exact ⟨by omega, hpr⟩
  have hp' : p ∈ pl521 := mem_pl521_of_mem_primesLE p hp521
  simp only [pl521, Finset.mem_insert, Finset.mem_singleton] at hp'
  rcases hp' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · have hser := log_sub_ge_series 2 (by norm_num)
    have hnum : (wlo 2 : Real) ≤ 1/((2 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((2 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((2 : Nat) : Real))^17 := by
      norm_num [show wloN 2 = -193161588 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 3 (by norm_num)
    have hnum : (wlo 3 : Real) ≤ 1/((3 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((3 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((3 : Nat) : Real))^17 := by
      norm_num [show wloN 3 = -72131790 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 5 (by norm_num)
    have hnum : (wlo 5 : Real) ≤ 1/((5 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((5 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((5 : Nat) : Real))^17 := by
      norm_num [show wloN 5 = -23143552 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 7 (by norm_num)
    have hnum : (wlo 7 : Real) ≤ 1/((7 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((7 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((7 : Nat) : Real))^17 := by
      norm_num [show wloN 7 = -11293537 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 11 (by norm_num)
    have hnum : (wlo 11 : Real) ≤ 1/((11 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((11 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((11 : Nat) : Real))^17 := by
      norm_num [show wloN 11 = -4401089 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 13 (by norm_num)
    have hnum : (wlo 13 : Real) ≤ 1/((13 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((13 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((13 : Nat) : Real))^17 := by
      norm_num [show wloN 13 = -3119631 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 17 (by norm_num)
    have hnum : (wlo 17 : Real) ≤ 1/((17 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((17 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((17 : Nat) : Real))^17 := by
      norm_num [show wloN 17 = -1801093 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 19 (by norm_num)
    have hnum : (wlo 19 : Real) ≤ 1/((19 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((19 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((19 : Nat) : Real))^17 := by
      norm_num [show wloN 19 = -1435643 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 23 (by norm_num)
    have hnum : (wlo 23 : Real) ≤ 1/((23 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((23 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((23 : Nat) : Real))^17 := by
      norm_num [show wloN 23 = -973502 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 29 (by norm_num)
    have hnum : (wlo 29 : Real) ≤ 1/((29 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((29 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((29 : Nat) : Real))^17 := by
      norm_num [show wloN 29 = -608562 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 31 (by norm_num)
    have hnum : (wlo 31 : Real) ≤ 1/((31 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((31 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((31 : Nat) : Real))^17 := by
      norm_num [show wloN 31 = -531759 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 37 (by norm_num)
    have hnum : (wlo 37 : Real) ≤ 1/((37 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((37 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((37 : Nat) : Real))^17 := by
      norm_num [show wloN 37 = -371948 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 41 (by norm_num)
    have hnum : (wlo 41 : Real) ≤ 1/((41 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((41 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((41 : Nat) : Real))^17 := by
      norm_num [show wloN 41 = -302369 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 43 (by norm_num)
    have hnum : (wlo 43 : Real) ≤ 1/((43 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((43 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((43 : Nat) : Real))^17 := by
      norm_num [show wloN 43 = -274684 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 47 (by norm_num)
    have hnum : (wlo 47 : Real) ≤ 1/((47 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((47 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((47 : Nat) : Real))^17 := by
      norm_num [show wloN 47 = -229610 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 53 (by norm_num)
    have hnum : (wlo 53 : Real) ≤ 1/((53 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((53 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((53 : Nat) : Real))^17 := by
      norm_num [show wloN 53 = -180271 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 59 (by norm_num)
    have hnum : (wlo 59 : Real) ≤ 1/((59 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((59 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((59 : Nat) : Real))^17 := by
      norm_num [show wloN 59 = -145281 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 61 (by norm_num)
    have hnum : (wlo 61 : Real) ≤ 1/((61 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((61 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((61 : Nat) : Real))^17 := by
      norm_num [show wloN 61 = -135860 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 67 (by norm_num)
    have hnum : (wlo 67 : Real) ≤ 1/((67 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((67 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((67 : Nat) : Real))^17 := by
      norm_num [show wloN 67 = -112505 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 71 (by norm_num)
    have hnum : (wlo 71 : Real) ≤ 1/((71 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((71 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((71 : Nat) : Real))^17 := by
      norm_num [show wloN 71 = -100128 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 73 (by norm_num)
    have hnum : (wlo 73 : Real) ≤ 1/((73 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((73 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((73 : Nat) : Real))^17 := by
      norm_num [show wloN 73 = -94692 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 79 (by norm_num)
    have hnum : (wlo 79 : Real) ≤ 1/((79 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((79 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((79 : Nat) : Real))^17 := by
      norm_num [show wloN 79 = -80798 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 83 (by norm_num)
    have hnum : (wlo 83 : Real) ≤ 1/((83 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((83 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((83 : Nat) : Real))^17 := by
      norm_num [show wloN 83 = -73168 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 89 (by norm_num)
    have hnum : (wlo 89 : Real) ≤ 1/((89 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((89 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((89 : Nat) : Real))^17 := by
      norm_num [show wloN 89 = -63601 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 97 (by norm_num)
    have hnum : (wlo 97 : Real) ≤ 1/((97 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((97 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((97 : Nat) : Real))^17 := by
      norm_num [show wloN 97 = -53509 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 101 (by norm_num)
    have hnum : (wlo 101 : Real) ≤ 1/((101 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((101 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((101 : Nat) : Real))^17 := by
      norm_num [show wloN 101 = -49341 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 103 (by norm_num)
    have hnum : (wlo 103 : Real) ≤ 1/((103 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((103 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((103 : Nat) : Real))^17 := by
      norm_num [show wloN 103 = -47438 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 107 (by norm_num)
    have hnum : (wlo 107 : Real) ≤ 1/((107 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((107 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((107 : Nat) : Real))^17 := by
      norm_num [show wloN 107 = -43946 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 109 (by norm_num)
    have hnum : (wlo 109 : Real) ≤ 1/((109 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((109 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((109 : Nat) : Real))^17 := by
      norm_num [show wloN 109 = -42344 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 113 (by norm_num)
    have hnum : (wlo 113 : Real) ≤ 1/((113 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((113 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((113 : Nat) : Real))^17 := by
      norm_num [show wloN 113 = -39390 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 127 (by norm_num)
    have hnum : (wlo 127 : Real) ≤ 1/((127 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((127 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((127 : Nat) : Real))^17 := by
      norm_num [show wloN 127 = -31164 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 131 (by norm_num)
    have hnum : (wlo 131 : Real) ≤ 1/((131 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((131 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((131 : Nat) : Real))^17 := by
      norm_num [show wloN 131 = -29285 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 137 (by norm_num)
    have hnum : (wlo 137 : Real) ≤ 1/((137 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((137 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((137 : Nat) : Real))^17 := by
      norm_num [show wloN 137 = -26771 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 139 (by norm_num)
    have hnum : (wlo 139 : Real) ≤ 1/((139 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((139 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((139 : Nat) : Real))^17 := by
      norm_num [show wloN 139 = -26004 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 149 (by norm_num)
    have hnum : (wlo 149 : Real) ≤ 1/((149 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((149 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((149 : Nat) : Real))^17 := by
      norm_num [show wloN 149 = -22623 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 151 (by norm_num)
    have hnum : (wlo 151 : Real) ≤ 1/((151 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((151 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((151 : Nat) : Real))^17 := by
      norm_num [show wloN 151 = -22027 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 157 (by norm_num)
    have hnum : (wlo 157 : Real) ≤ 1/((157 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((157 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((157 : Nat) : Real))^17 := by
      norm_num [show wloN 157 = -20372 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 163 (by norm_num)
    have hnum : (wlo 163 : Real) ≤ 1/((163 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((163 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((163 : Nat) : Real))^17 := by
      norm_num [show wloN 163 = -18897 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 167 (by norm_num)
    have hnum : (wlo 167 : Real) ≤ 1/((167 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((167 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((167 : Nat) : Real))^17 := by
      norm_num [show wloN 167 = -18001 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 173 (by norm_num)
    have hnum : (wlo 173 : Real) ≤ 1/((173 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((173 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((173 : Nat) : Real))^17 := by
      norm_num [show wloN 173 = -16771 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 179 (by norm_num)
    have hnum : (wlo 179 : Real) ≤ 1/((179 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((179 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((179 : Nat) : Real))^17 := by
      norm_num [show wloN 179 = -15664 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 181 (by norm_num)
    have hnum : (wlo 181 : Real) ≤ 1/((181 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((181 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((181 : Nat) : Real))^17 := by
      norm_num [show wloN 181 = -15319 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 191 (by norm_num)
    have hnum : (wlo 191 : Real) ≤ 1/((191 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((191 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((191 : Nat) : Real))^17 := by
      norm_num [show wloN 191 = -13754 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 193 (by norm_num)
    have hnum : (wlo 193 : Real) ≤ 1/((193 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((193 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((193 : Nat) : Real))^17 := by
      norm_num [show wloN 193 = -13470 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 197 (by norm_num)
    have hnum : (wlo 197 : Real) ≤ 1/((197 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((197 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((197 : Nat) : Real))^17 := by
      norm_num [show wloN 197 = -12928 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 199 (by norm_num)
    have hnum : (wlo 199 : Real) ≤ 1/((199 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((199 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((199 : Nat) : Real))^17 := by
      norm_num [show wloN 199 = -12669 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 211 (by norm_num)
    have hnum : (wlo 211 : Real) ≤ 1/((211 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((211 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((211 : Nat) : Real))^17 := by
      norm_num [show wloN 211 = -11267 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 223 (by norm_num)
    have hnum : (wlo 223 : Real) ≤ 1/((223 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((223 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((223 : Nat) : Real))^17 := by
      norm_num [show wloN 223 = -10085 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 227 (by norm_num)
    have hnum : (wlo 227 : Real) ≤ 1/((227 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((227 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((227 : Nat) : Real))^17 := by
      norm_num [show wloN 227 = -9732 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 229 (by norm_num)
    have hnum : (wlo 229 : Real) ≤ 1/((229 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((229 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((229 : Nat) : Real))^17 := by
      norm_num [show wloN 229 = -9563 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 233 (by norm_num)
    have hnum : (wlo 233 : Real) ≤ 1/((233 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((233 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((233 : Nat) : Real))^17 := by
      norm_num [show wloN 233 = -9237 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 239 (by norm_num)
    have hnum : (wlo 239 : Real) ≤ 1/((239 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((239 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((239 : Nat) : Real))^17 := by
      norm_num [show wloN 239 = -8778 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 241 (by norm_num)
    have hnum : (wlo 241 : Real) ≤ 1/((241 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((241 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((241 : Nat) : Real))^17 := by
      norm_num [show wloN 241 = -8633 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 251 (by norm_num)
    have hnum : (wlo 251 : Real) ≤ 1/((251 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((251 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((251 : Nat) : Real))^17 := by
      norm_num [show wloN 251 = -7958 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 257 (by norm_num)
    have hnum : (wlo 257 : Real) ≤ 1/((257 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((257 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((257 : Nat) : Real))^17 := by
      norm_num [show wloN 257 = -7590 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 263 (by norm_num)
    have hnum : (wlo 263 : Real) ≤ 1/((263 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((263 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((263 : Nat) : Real))^17 := by
      norm_num [show wloN 263 = -7248 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 269 (by norm_num)
    have hnum : (wlo 269 : Real) ≤ 1/((269 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((269 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((269 : Nat) : Real))^17 := by
      norm_num [show wloN 269 = -6927 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 271 (by norm_num)
    have hnum : (wlo 271 : Real) ≤ 1/((271 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((271 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((271 : Nat) : Real))^17 := by
      norm_num [show wloN 271 = -6825 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 277 (by norm_num)
    have hnum : (wlo 277 : Real) ≤ 1/((277 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((277 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((277 : Nat) : Real))^17 := by
      norm_num [show wloN 277 = -6533 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 281 (by norm_num)
    have hnum : (wlo 281 : Real) ≤ 1/((281 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((281 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((281 : Nat) : Real))^17 := by
      norm_num [show wloN 281 = -6348 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 283 (by norm_num)
    have hnum : (wlo 283 : Real) ≤ 1/((283 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((283 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((283 : Nat) : Real))^17 := by
      norm_num [show wloN 283 = -6258 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 293 (by norm_num)
    have hnum : (wlo 293 : Real) ≤ 1/((293 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((293 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((293 : Nat) : Real))^17 := by
      norm_num [show wloN 293 = -5838 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 307 (by norm_num)
    have hnum : (wlo 307 : Real) ≤ 1/((307 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((307 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((307 : Nat) : Real))^17 := by
      norm_num [show wloN 307 = -5317 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 311 (by norm_num)
    have hnum : (wlo 311 : Real) ≤ 1/((311 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((311 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((311 : Nat) : Real))^17 := by
      norm_num [show wloN 311 = -5181 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 313 (by norm_num)
    have hnum : (wlo 313 : Real) ≤ 1/((313 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((313 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((313 : Nat) : Real))^17 := by
      norm_num [show wloN 313 = -5115 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 317 (by norm_num)
    have hnum : (wlo 317 : Real) ≤ 1/((317 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((317 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((317 : Nat) : Real))^17 := by
      norm_num [show wloN 317 = -4987 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 331 (by norm_num)
    have hnum : (wlo 331 : Real) ≤ 1/((331 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((331 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((331 : Nat) : Real))^17 := by
      norm_num [show wloN 331 = -4573 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 337 (by norm_num)
    have hnum : (wlo 337 : Real) ≤ 1/((337 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((337 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((337 : Nat) : Real))^17 := by
      norm_num [show wloN 337 = -4412 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 347 (by norm_num)
    have hnum : (wlo 347 : Real) ≤ 1/((347 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((347 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((347 : Nat) : Real))^17 := by
      norm_num [show wloN 347 = -4161 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 349 (by norm_num)
    have hnum : (wlo 349 : Real) ≤ 1/((349 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((349 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((349 : Nat) : Real))^17 := by
      norm_num [show wloN 349 = -4113 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 353 (by norm_num)
    have hnum : (wlo 353 : Real) ≤ 1/((353 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((353 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((353 : Nat) : Real))^17 := by
      norm_num [show wloN 353 = -4021 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 359 (by norm_num)
    have hnum : (wlo 359 : Real) ≤ 1/((359 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((359 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((359 : Nat) : Real))^17 := by
      norm_num [show wloN 359 = -3887 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 367 (by norm_num)
    have hnum : (wlo 367 : Real) ≤ 1/((367 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((367 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((367 : Nat) : Real))^17 := by
      norm_num [show wloN 367 = -3720 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 373 (by norm_num)
    have hnum : (wlo 373 : Real) ≤ 1/((373 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((373 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((373 : Nat) : Real))^17 := by
      norm_num [show wloN 373 = -3601 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 379 (by norm_num)
    have hnum : (wlo 379 : Real) ≤ 1/((379 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((379 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((379 : Nat) : Real))^17 := by
      norm_num [show wloN 379 = -3488 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 383 (by norm_num)
    have hnum : (wlo 383 : Real) ≤ 1/((383 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((383 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((383 : Nat) : Real))^17 := by
      norm_num [show wloN 383 = -3415 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 389 (by norm_num)
    have hnum : (wlo 389 : Real) ≤ 1/((389 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((389 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((389 : Nat) : Real))^17 := by
      norm_num [show wloN 389 = -3310 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 397 (by norm_num)
    have hnum : (wlo 397 : Real) ≤ 1/((397 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((397 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((397 : Nat) : Real))^17 := by
      norm_num [show wloN 397 = -3178 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 401 (by norm_num)
    have hnum : (wlo 401 : Real) ≤ 1/((401 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((401 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((401 : Nat) : Real))^17 := by
      norm_num [show wloN 401 = -3115 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 409 (by norm_num)
    have hnum : (wlo 409 : Real) ≤ 1/((409 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((409 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((409 : Nat) : Real))^17 := by
      norm_num [show wloN 409 = -2994 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 419 (by norm_num)
    have hnum : (wlo 419 : Real) ≤ 1/((419 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((419 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((419 : Nat) : Real))^17 := by
      norm_num [show wloN 419 = -2853 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 421 (by norm_num)
    have hnum : (wlo 421 : Real) ≤ 1/((421 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((421 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((421 : Nat) : Real))^17 := by
      norm_num [show wloN 421 = -2826 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 431 (by norm_num)
    have hnum : (wlo 431 : Real) ≤ 1/((431 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((431 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((431 : Nat) : Real))^17 := by
      norm_num [show wloN 431 = -2696 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 433 (by norm_num)
    have hnum : (wlo 433 : Real) ≤ 1/((433 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((433 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((433 : Nat) : Real))^17 := by
      norm_num [show wloN 433 = -2671 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 439 (by norm_num)
    have hnum : (wlo 439 : Real) ≤ 1/((439 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((439 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((439 : Nat) : Real))^17 := by
      norm_num [show wloN 439 = -2599 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 443 (by norm_num)
    have hnum : (wlo 443 : Real) ≤ 1/((443 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((443 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((443 : Nat) : Real))^17 := by
      norm_num [show wloN 443 = -2552 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 449 (by norm_num)
    have hnum : (wlo 449 : Real) ≤ 1/((449 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((449 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((449 : Nat) : Real))^17 := by
      norm_num [show wloN 449 = -2484 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 457 (by norm_num)
    have hnum : (wlo 457 : Real) ≤ 1/((457 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((457 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((457 : Nat) : Real))^17 := by
      norm_num [show wloN 457 = -2398 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 461 (by norm_num)
    have hnum : (wlo 461 : Real) ≤ 1/((461 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((461 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((461 : Nat) : Real))^17 := by
      norm_num [show wloN 461 = -2357 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 463 (by norm_num)
    have hnum : (wlo 463 : Real) ≤ 1/((463 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((463 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((463 : Nat) : Real))^17 := by
      norm_num [show wloN 463 = -2336 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 467 (by norm_num)
    have hnum : (wlo 467 : Real) ≤ 1/((467 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((467 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((467 : Nat) : Real))^17 := by
      norm_num [show wloN 467 = -2296 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 479 (by norm_num)
    have hnum : (wlo 479 : Real) ≤ 1/((479 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((479 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((479 : Nat) : Real))^17 := by
      norm_num [show wloN 479 = -2183 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 487 (by norm_num)
    have hnum : (wlo 487 : Real) ≤ 1/((487 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((487 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((487 : Nat) : Real))^17 := by
      norm_num [show wloN 487 = -2112 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 491 (by norm_num)
    have hnum : (wlo 491 : Real) ≤ 1/((491 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((491 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((491 : Nat) : Real))^17 := by
      norm_num [show wloN 491 = -2077 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 499 (by norm_num)
    have hnum : (wlo 499 : Real) ≤ 1/((499 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((499 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((499 : Nat) : Real))^17 := by
      norm_num [show wloN 499 = -2011 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 503 (by norm_num)
    have hnum : (wlo 503 : Real) ≤ 1/((503 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((503 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((503 : Nat) : Real))^17 := by
      norm_num [show wloN 503 = -1979 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · have hser := log_sub_ge_series 509 (by norm_num)
    have hnum : (wlo 509 : Real) ≤ 1/((509 : Nat) : Real) - (∑ i ∈ Finset.range 16, (1/((509 : Nat) : Real))^(i+1)/(i+1)) - 2*(1/((509 : Nat) : Real))^17 := by
      norm_num [show wloN 509 = -1933 by rfl, wlo, Finset.sum_range_succ, Finset.sum_range_zero]
    linarith

  · exact absurd hle (by norm_num)


private lemma WLO_eq_q : ∀ n, n ≤ 512 → (∑ p ∈ Nat.primesLE n, wlo p) = WLO n := by
  intro n
  induction n with
  | zero => intro _; simp [WLO, WLOi, Nat.primesLE]
  | succ k ih =>
    intro hk
    rw [sum_primesLE_succ k wlo, ih (by omega)]
    by_cases h : (k+1).Prime
    · rw [if_pos h,
          show WLO k = (WLOi k : Rat)/1000000000 from rfl,
          show WLO (k+1) = ((WLOi k + (if (k+1).Prime then wloN (k+1) else 0) : Int) : Rat)/1000000000 from rfl,
          show wlo (k+1) = (wloN (k+1) : Rat)/1000000000 from rfl,
          if_pos h]
      push_cast
      ring
    · rw [if_neg h,
          show WLO k = (WLOi k : Rat)/1000000000 from rfl,
          show WLO (k+1) = ((WLOi k + (if (k+1).Prime then wloN (k+1) else 0) : Int) : Rat)/1000000000 from rfl,
          if_neg h]
      push_cast
      ring


theorem solution :
    (WLO 512 : Real) ≤ ∑ p ∈ Nat.primesLE 512, (Real.log (1 - 1/(p:Real)) + 1/(p:Real)) := by
  have h1 : (∑ p ∈ Nat.primesLE 512, wlo p) = WLO 512 := WLO_eq_q 512 (le_refl 512)
  rw [← h1]
  push_cast
  apply Finset.sum_le_sum
  intro p hp
  exact wlo_le_w_of_mem p hp

