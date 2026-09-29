-- Prove2me | solution 2 for OddPerfectNumber.dris_packaged_congruent_absurd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-12T11:25:10.315637+00:00
-- url     : https://prove2.me/submissions/ee37117b-64a0-4ce4-9590-5ee3151915e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_OddPerfectNumber_packaged_N_perfect
import Theorems.Thm_OddPerfectNumber_no_odd_perfect_special_exponent_one
import Theorems.Thm_OddPerfectNumber_no_odd_perfect_special_exponent_ge_five

open OddPerfectNumber

theorem solution (p k m s t d : Nat)
    (hp : p.Prime) (hm : Odd m) (hpm : ¬ p ∣ m) (hs_odd : Odd s)
    (hp4 : p % 4 = 1) (hk4 : k % 4 = 1)
    (hsig : (∑ d ∈ (p ^ k).divisors, d) = 2 * t)
    (hdvd : m ^ 2 = t * d)
    (hsigm : (∑ x ∈ (m ^ 2).divisors, x) = p ^ k * d)
    (hd_dvd : d ∣ m ^ 2) : False := by
  have hN : Nat.Perfect (p ^ k * m ^ 2) :=
    packaged_N_perfect p k m t d hp hm hpm hsig hdvd hsigm
  have hp2 : p ≠ 2 := by
    intro h
    subst p
    norm_num at hp4
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have hNodd : Odd (p ^ k * m ^ 2) := (hpodd.pow).mul hm.pow
  by_cases hk1 : k = 1
  · have hN1 : Nat.Perfect (p * m ^ 2) := by simpa [hk1] using hN
    have hNodd1 : Odd (p * m ^ 2) := by simpa [hk1] using hNodd
    exact (no_odd_perfect_special_exponent_one
      (p * m ^ 2) p m hN1 hNodd1 hp hp4 hpm) rfl
  · have hk5 : 5 ≤ k := by omega
    exact (no_odd_perfect_special_exponent_ge_five
      (p ^ k * m ^ 2) p k m hN hNodd hp hp4 hk4 hk5 hpm) rfl
