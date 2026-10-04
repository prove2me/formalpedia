-- Prove2me | solution 1 for OddPerfectNumber.k_one_q2_five_q3_twentythree_large_D_D_le_685_v4
-- status  : ACCEPTED   (prove)
-- author  : @Patrick
-- created : 2026-09-18T08:57:12.302348+00:00
-- url     : https://prove2.me/submissions/a66e9f03-928c-4673-890b-71015a973c0f

import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.Ring

private theorem geom_upper (q n : Nat) (hq : 1 ≤ q) :
    (q - 1) * (∑ i ∈ Finset.range (n + 1), q ^ i) ≤ q * q ^ n := by
  calc
    _ = q ^ (n + 1) - 1 := by rw [mul_comm, geom_sum_mul_of_one_le hq]
    _ ≤ q ^ (n + 1) := Nat.sub_le _ _
    _ = q * q ^ n := by rw [pow_succ, mul_comm]

theorem solution (m a b c e D p q4 sigma : Nat) (hfac : m ^ 2 = 3 ^ (2*a) * 5 ^ (2*b) * 23 ^ (2*c) * q4 ^ (2*e)) (hsigma : sigma = (∑ i ∈ Finset.range (2*a + 1), 3 ^ i) * (∑ i ∈ Finset.range (2*b + 1), 5 ^ i) * (∑ i ∈ Finset.range (2*c + 1), 23 ^ i) * (∑ i ∈ Finset.range (2*e + 1), q4 ^ i)) (hrel : D * sigma = p * m ^ 2) (hDlow : 111 ≤ D) (hDodd : Odd D) (hp : p.Prime) (hp4 : p % 4 = 1) (hp_eq : p = 2 * D - 1) (hq4prime : q4.Prime) (hq4gt47 : 47 < q4) (hq4le : q4 ≤ 61) (hq4dvd : q4 ∣ D) (hDsupport : ∀ r, r.Prime → r ∣ D → r = 3 ∨ r = 5 ∨ r = 23 ∨ r = q4) (ha : 5 ≤ a) (hb : 3 ≤ b) (hc : 4 ≤ c) (he : 1 ≤ e) : D ≤ 685 := by
  have hqcheck : ∀ q : Fin 62, q.val.Prime → 47 < q.val →
      q.val = 53 ∨ q.val = 59 ∨ q.val = 61 := by decide +kernel
  have hqcases := hqcheck ⟨q4, by omega⟩ hq4prime hq4gt47
  change q4 = 53 ∨ q4 = 59 ∨ q4 = 61 at hqcases
  have h3 := geom_upper 3 (2*a) (by decide)
  have h5 := geom_upper 5 (2*b) (by decide)
  have h23 := geom_upper 23 (2*c) (by decide)
  have hq : 52 * (∑ i ∈ Finset.range (2*e+1), q4 ^ i) ≤ 53 * q4 ^ (2*e) := by
    have hu := geom_upper q4 (2*e) (by omega)
    rcases hqcases with rfl | rfl | rfl <;> omega
  have hmul := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul h3 h5) h23) hq
  have hcross : 9152 * sigma ≤ 18285 * m ^ 2 := by
    rw [hfac, hsigma]
    convert hmul using 1 <;> ring
  have hmpos : 0 < m ^ 2 := by
    rw [hfac]
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.pow_pos (by decide))
      (Nat.pow_pos (by decide))) (Nat.pow_pos (by decide))) (Nat.pow_pos (by omega))
  have hineq : 9152 * p * m ^ 2 ≤ 18285 * D * m ^ 2 := by
    calc
      9152 * p * m ^ 2 = 9152 * (D * sigma) := by rw [hrel]; ring
      _ = D * (9152 * sigma) := by ring
      _ ≤ D * (18285 * m ^ 2) := Nat.mul_le_mul_left D hcross
      _ = 18285 * D * m ^ 2 := by ring
  have hbound := le_of_mul_le_mul_right hineq hmpos
  rw [hp_eq] at hbound
  have hstrong : D ≤ 481 := by omega
  omega

/-- info: 'solution' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms solution
