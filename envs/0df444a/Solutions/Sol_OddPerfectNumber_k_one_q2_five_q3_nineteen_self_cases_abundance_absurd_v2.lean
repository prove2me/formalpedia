-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_nineteen_self_cases_abundance_absurd_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-16T20:39:26.593708+00:00
-- url     : https://prove2.me/submissions/27ae2359-654d-499b-9b2f-5785fcf0f543

import Mathlib
import Theorems.Thm_OddPerfectNumber_geom_sum_cross_lt_of_le

theorem solution (m a b c e D p q4 sigma : Nat)
    (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 19 ^ (2*c) * q4 ^ (2*e))
    (hsigma : sigma =
      (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) *
      (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) *
      (∑ i ∈ Finset.range (2*c + 1), 19 ^ i) *
      (∑ i ∈ Finset.range (2*e + 1), q4 ^ i))
    (hrel : D * sigma = p * m ^ 2)
    (hcases :
      (D = 157 ∧ q4 = 157 ∧ p = 313) ∨
      (D = 199 ∧ q4 = 199 ∧ p = 397) ∨
      (D = 211 ∧ q4 = 211 ∧ p = 421))
    (ha : 4 ≤ a) (hb : 3 ≤ b) (hc : 2 ≤ c) (he : 1 ≤ e)
    (hq4prime : q4.Prime) : False := by
  let S3 := ∑ i ∈ Finset.range (2*a + 1), 3 ^ i
  let S5 := ∑ i ∈ Finset.range (2*b + 1), 5 ^ i
  let S19 := ∑ i ∈ Finset.range (2*c + 1), 19 ^ i
  let Sq := ∑ i ∈ Finset.range (2*e + 1), q4 ^ i
  have hu3 := OddPerfectNumber.geom_sum_cross_lt_of_le 3 3 (2*a)
    (by norm_num) (by norm_num) (by norm_num)
  have hu5 := OddPerfectNumber.geom_sum_cross_lt_of_le 5 5 (2*b)
    (by norm_num) (by norm_num) (by norm_num)
  have hu19 := OddPerfectNumber.geom_sum_cross_lt_of_le 19 19 (2*c)
    (by norm_num) (by norm_num) (by norm_num)
  have hq4two : 2 ≤ q4 := hq4prime.two_le
  have huq := OddPerfectNumber.geom_sum_cross_lt_of_le q4 q4 (2*e)
    hq4two (by rfl) hq4prime
  have hu35 := Nat.mul_lt_mul_of_lt_of_lt hu3 hu5
  have hu19q := Nat.mul_lt_mul_of_lt_of_lt hu19 huq
  have hu := Nat.mul_lt_mul_of_lt_of_lt hu35 hu19q
  have hupper : 144 * (q4 - 1) * sigma < 285 * q4 * (m ^ 2) := by
    calc
      144 * (q4 - 1) * sigma =
          (2*S3) * (4*S5) * (18*S19) * ((q4-1)*Sq) := by
            rw [hsigma]
            dsimp [S3, S5, S19, Sq]
            ring
      _ < (3*3^(2*a)) * (5*5^(2*b)) *
          ((19*19^(2*c)) * (q4*q4^(2*e))) := by
            simpa [S3, S5, S19, Sq, Nat.mul_assoc] using hu
      _ = 285 * q4 * (m ^ 2) := by
            rw [hfac]
            ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    positivity
  rcases hcases with h157 | h199 | h211
  · rcases h157 with ⟨rfl, rfl, rfl⟩
    have hmul := (Nat.mul_lt_mul_left (by norm_num : 0 < (157 : Nat))).2 hupper
    have hstrict :
        144 * (157 - 1) * 313 * (m ^ 2) <
          (285 * 157 * 157) * (m ^ 2) := by
      calc
        144 * (157 - 1) * 313 * (m ^ 2) =
            144 * (157 - 1) * (313 * (m ^ 2)) := by ring
        _ = 144 * (157 - 1) * (157 * sigma) := by rw [hrel]
        _ = 157 * (144 * (157 - 1) * sigma) := by ring
        _ < 157 * (285 * 157 * (m ^ 2)) := by simpa [Nat.mul_assoc] using hmul
        _ = (285 * 157 * 157) * (m ^ 2) := by ring
    have hcoef : 144 * (157 - 1) * 313 < 285 * 157 * 157 := by
      exact Nat.lt_of_mul_lt_mul_right hstrict
    norm_num at hcoef
  · rcases h199 with ⟨rfl, rfl, rfl⟩
    have hmul := (Nat.mul_lt_mul_left (by norm_num : 0 < (199 : Nat))).2 hupper
    have hstrict :
        144 * (199 - 1) * 397 * (m ^ 2) <
          (285 * 199 * 199) * (m ^ 2) := by
      calc
        144 * (199 - 1) * 397 * (m ^ 2) =
            144 * (199 - 1) * (397 * (m ^ 2)) := by ring
        _ = 144 * (199 - 1) * (199 * sigma) := by rw [hrel]
        _ = 199 * (144 * (199 - 1) * sigma) := by ring
        _ < 199 * (285 * 199 * (m ^ 2)) := by simpa [Nat.mul_assoc] using hmul
        _ = (285 * 199 * 199) * (m ^ 2) := by ring
    have hcoef : 144 * (199 - 1) * 397 < 285 * 199 * 199 := by
      exact Nat.lt_of_mul_lt_mul_right hstrict
    norm_num at hcoef
  · rcases h211 with ⟨rfl, rfl, rfl⟩
    have hmul := (Nat.mul_lt_mul_left (by norm_num : 0 < (211 : Nat))).2 hupper
    have hstrict :
        144 * (211 - 1) * 421 * (m ^ 2) <
          (285 * 211 * 211) * (m ^ 2) := by
      calc
        144 * (211 - 1) * 421 * (m ^ 2) =
            144 * (211 - 1) * (421 * (m ^ 2)) := by ring
        _ = 144 * (211 - 1) * (211 * sigma) := by rw [hrel]
        _ = 211 * (144 * (211 - 1) * sigma) := by ring
        _ < 211 * (285 * 211 * (m ^ 2)) := by simpa [Nat.mul_assoc] using hmul
        _ = (285 * 211 * 211) * (m ^ 2) := by ring
    have hcoef : 144 * (211 - 1) * 421 < 285 * 211 * 211 := by
      exact Nat.lt_of_mul_lt_mul_right hstrict
    norm_num at hcoef
