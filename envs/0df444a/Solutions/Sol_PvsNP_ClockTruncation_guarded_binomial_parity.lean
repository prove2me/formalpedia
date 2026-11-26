-- Prove2me | solution 1 for PvsNP.ClockTruncation.guarded_binomial_parity
-- status  : ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-26T17:17:53.998565+00:00
-- url     : https://prove2.me/submissions/7055b7c8-4836-4824-9844-d26fa48e5d6d

import Mathlib.Data.Nat.Choose.Lucas

set_option autoImplicit false

namespace PvsNP.ClockTruncationLocal

private theorem choose_mod_two (n k : ℕ) :
    n.choose k % 2 = ((n%2).choose (k%2) * (n/2).choose (k/2)) % 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact Choose.choose_modEq_choose_mod_mul_choose_div_nat

/-- The binomial coefficient is odd exactly when addition needs no binary carries. -/
theorem choose_add_mod_two_eq_one_iff (s q : ℕ) :
    (s+q).choose s % 2 = 1 ↔ s &&& q = 0 := by
  by_cases zero : s+q = 0
  · have hs : s = 0 := by omega
    have hq : q = 0 := by omega
    simp [hs,hq]
  have decrease : s/2+q/2 < s+q := by omega
  rw [choose_mod_two]
  rcases (show s%2 = 0 ∨ s%2 = 1 by omega) with evenS | oddS
  · have half : (s+q)/2 = s/2+q/2 := by omega
    have low : (s &&& q)%2 = 0 := by
      have notOne : (s &&& q)%2 ≠ 1 := by
        intro bitOne
        have both := Nat.and_mod_two_eq_one.mp bitOne
        omega
      omega
    simp only [evenS,Nat.choose_zero_right,one_mul,half]
    rw [choose_add_mod_two_eq_one_iff (s/2) (q/2),← Nat.and_div_two]
    omega
  · rcases (show q%2 = 0 ∨ q%2 = 1 by omega) with evenQ | oddQ
    · have half : (s+q)/2 = s/2+q/2 := by omega
      have loSum : (s+q)%2 = 1 := by omega
      have low : (s &&& q)%2 = 0 := by
        have notOne : (s &&& q)%2 ≠ 1 := by
          intro bitOne
          have both := Nat.and_mod_two_eq_one.mp bitOne
          omega
        omega
      simp only [loSum,oddS,Nat.choose_self,one_mul,half]
      rw [choose_add_mod_two_eq_one_iff (s/2) (q/2),← Nat.and_div_two]
      omega
    · have loSum : (s+q)%2 = 0 := by omega
      have low : (s &&& q)%2 = 1 := Nat.and_mod_two_eq_one.mpr ⟨oddS,oddQ⟩
      simp only [loSum,oddS,Nat.choose_zero_succ,zero_mul,Nat.zero_mod]
      omega
termination_by s+q

theorem choose_add_mod_two_eq (s q : ℕ) :
    (s+q).choose s % 2 = if s &&& q = 0 then 1 else 0 := by
  split_ifs with noCarry
  · exact (choose_add_mod_two_eq_one_iff s q).mpr noCarry
  · have notOne : (s+q).choose s % 2 ≠ 1 :=
      fun odd => noCarry ((choose_add_mod_two_eq_one_iff s q).mp odd)
    omega

theorem low_sub_of_le {m t d : ℕ} (hd : d ≤ t) (small : d < m) :
    (t-d)%m = (t%m+m-d)%m := by
  have h₁ : t ≡ t%m [MOD m] := (Nat.mod_modEq t m).symm
  have h₂ : t%m + m ≡ t%m [MOD m] := by
    change (t%m + m)%m = (t%m)%m
    simp
  exact (h₁.trans h₂.symm).sub_right hd (by omega)

theorem and_eq_low_and (s q w : ℕ) (hq : q < 2^w) :
    s &&& q = (s % 2^w) &&& q := by
  have h := Nat.and_mod_two_pow (a := s) (b := q) (n := w)
  simpa only [Nat.mod_eq_of_lt hq, Nat.mod_eq_of_lt (Nat.and_lt_two_pow s hq)] using h


end PvsNP.ClockTruncationLocal

open PvsNP.ClockTruncationLocal

theorem solution {w t d q : ℕ} (hd : d < 2^w) (hq : q < 2^w) :
    (if d ≤ t then (t-d+q).choose (t-d)%2 else 0) =
      if 2^w ≤ t ∨ d ≤ t % 2^w then
        (if (((t%2^w+2^w-d)%2^w) &&& q) = 0 then 1 else 0)
      else 0 := by
  have reaches : d ≤ t ↔ (2^w ≤ t ∨ d ≤ t%2^w) := by
    by_cases high : 2^w ≤ t
    · simp [high, hd.le.trans high]
    · have lt : t < 2^w := Nat.lt_of_not_ge high
      simp [high, Nat.mod_eq_of_lt lt]
  by_cases reached : d ≤ t
  · simp only [if_pos reached, if_pos (reaches.mp reached)]
    rw [choose_add_mod_two_eq,
      and_eq_low_and (t-d) q w hq, low_sub_of_le reached hd]
  · simp only [if_neg reached, if_neg (fun h => reached (reaches.mpr h))]
