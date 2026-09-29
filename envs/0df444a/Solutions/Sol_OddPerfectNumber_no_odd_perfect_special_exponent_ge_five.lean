-- Prove2me | solution 1 for OddPerfectNumber.no_odd_perfect_special_exponent_ge_five
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Gabewhigham
-- created : 2026-09-08T11:19:04.899113+00:00
-- url     : https://prove2.me/submissions/583be1c3-0c47-4518-a748-d4c3aa69b7d5
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_OddPerfectNumber_no_euler_equation_special_exponent_five
import Theorems.Thm_OddPerfectNumber_no_euler_equation_special_exponent_ge_nine

open OddPerfectNumber

theorem solution (n p k m : ℕ) (hn : Nat.Perfect n) (hodd : Odd n)
    (hp : p.Prime) (hp4 : p % 4 = 1) (hk4 : k % 4 = 1) (hk5 : 5 ≤ k) (hpm : ¬ p ∣ m) :
    n ≠ p ^ k * m ^ 2 := by
  intro hne
  subst hne
  have hsq : Odd (m ^ 2) := (Nat.odd_mul.mp hodd).2
  have hm : Odd m := by
    rw [sq] at hsq
    exact (Nat.odd_mul.mp hsq).1
  have hcop : Nat.Coprime (p ^ k) (m ^ 2) :=
    Nat.Coprime.pow k 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpm)
  have hsum : (∑ d ∈ (p ^ k).divisors, d) * (∑ d ∈ (m ^ 2).divisors, d)
      = 2 * (p ^ k * m ^ 2) := by
    rw [← Nat.Coprime.sum_divisors_mul hcop]
    exact (Nat.perfect_iff_sum_divisors_eq_two_mul hn.2).1 hn
  rcases (show k = 5 ∨ 9 ≤ k by omega) with rfl | h9
  · exact no_euler_equation_special_exponent_five p m hp hp4 hm hpm hsum
  · exact no_euler_equation_special_exponent_ge_nine p k m hp hp4 hk4 h9 hm hpm hsum
