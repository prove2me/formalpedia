-- Prove2me | solution 4 for WeakGoldbach.three_odd_primes_ge_exp3100
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @flyingviper
-- created : 2026-11-11T00:03:14.907211+00:00
-- url     : https://prove2.me/submissions/0765ff3d-24af-49da-9b67-245336e60afd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_Helfgott_weighted_count_lower
import Theorems.Thm_Helfgott_three_odd_primes_of_weighted_count
import Theorems.Thm_Helfgott_etaPlus_abs_le
import Theorems.Thm_Helfgott_etaStar_abs_le
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

open scoped BigOperators

-- The analytic lower bound already covers every odd n >= 10^27.
-- Its use below is a tracked open dependency, not a proof of that estimate.
theorem solution (n : ℕ) (hn : Real.exp 3100 ≤ (n : ℝ)) (hodd : Odd n) :
    ∃ p q r : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  have hbase : (101 : ℝ) ≤ Real.exp 100 := by
    linarith [Real.add_one_le_exp (100 : ℝ)]
  have hfloor : (10 : ℝ) ^ 27 ≤ Real.exp 3100 := by
    calc
      (10 : ℝ) ^ 27 ≤ 101 ^ 31 := by norm_num
      _ ≤ (Real.exp 100) ^ 31 := pow_le_pow_left₀ (by norm_num) hbase 31
      _ = Real.exp 3100 := by rw [← Real.exp_nat_mul]; norm_num
  have hlo : 10 ^ 27 ≤ n := by exact_mod_cast hfloor.trans hn
  have hcount := Helfgott.weighted_count_lower n hlo hodd
  exact Helfgott.three_odd_primes_of_weighted_count _ _
    (fun k => Helfgott.etaPlus_abs_le _) (fun k => Helfgott.etaStar_abs_le _)
    n hlo hcount
