-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_two_prime_index_not_three_mod_twelve
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T16:32:28.342559+00:00
-- url     : https://prove2.me/submissions/665cf1c1-ca6b-4f12-8e7d-a2bd8312e572

import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_vp_three_of_mod_one
import Theorems.Thm_OddPerfectNumber_Kernel_vp_three_of_mod_two

set_option linter.unusedVariables false
set_option linter.unnecessarySimpa false
set_option linter.unusedSimpArgs false

open OddPerfectNumber.Kernel

theorem solution (p m d1 q r : Nat)
    (hp : p.Prime) (hp2 : p != 2) (hp4 : p % 4 = 1) (hm : Odd m)
    (hpm : Not (Dvd.dvd p m)) (hq : q.Prime) (hr : r.Prime) (hqr : q < r)
    (hq3 : q != 3) (hr3 : r != 3)
    (h1 : 2 * m ^ 2 =
      (2 * (p ^ 2 + p + 1) * ((p + 1) / 2 * (p ^ 2 - p + 1))) * (d1 ^ 2 * (q * r))) :
    p % 12 = 5 := by
  have hpne2 : p ≠ 2 := by
    intro h
    simp [h] at hp2
  have hpne3 : p ≠ 3 := by
    intro h
    simp [h] at hp4
  have hqne3 : q ≠ 3 := by
    intro h
    simp [h] at hq3
  have hrne3 : r ≠ 3 := by
    intro h
    simp [h] at hr3
  have hmod : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
  rcases hmod with h0 | h1mod | h2mod
  · have hdiv : 3 ∣ p := (Nat.dvd_iff_mod_eq_zero).2 h0
    have hp3 : 3 = p :=
      (Nat.prime_dvd_prime_iff_eq (by decide : (3 : Nat).Prime) hp).1 hdiv
    exfalso
    exact hpne3 hp3.symm
  · -- p ≡ 1 mod 3 makes v_3 of the right-hand side odd, while v_3(m^2) is even.
    let A : Nat := p ^ 2 + p + 1
    let B : Nat := (p + 1) / 2
    let C : Nat := p ^ 2 - p + 1
    let D : Nat := d1 ^ 2
    have hfac : m ^ 2 = A * B * C * D * q * r := by
      have h2 : 2 * m ^ 2 = 2 * (A * B * C * D * q * r) := by
        simpa [A, B, C, D, mul_assoc, mul_left_comm, mul_comm] using h1
      exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2) h2
    have hA : A.factorization 3 = 1 := vp_three_of_mod_one p h1mod
    have hC0 : ¬ 3 ∣ C := by
      intro hd
      have hmod0 : C % 3 = 0 := (Nat.dvd_iff_mod_eq_zero).1 hd
      have hk : p = 3 * (p / 3) + 1 := by omega
      set k := p / 3
      have hCeq : C = 3 * (3 * k ^ 2 + k) + 1 := by
        simp [C]
        rw [hk]
        refine (Nat.sub_eq_iff_eq_add ?_).2 ?_
        · nlinarith
        · ring
      rw [hCeq] at hmod0
      omega
    have hC : C.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hC0
    have hB0 : ¬ 3 ∣ B := by
      intro hd
      have hodd : Odd p := hp.odd_of_ne_two hpne2
      have heven : Even (p + 1) := by
        rw [Nat.even_add_one]
        exact Nat.not_even_iff_odd.2 hodd
      have hsplit : 2 * B = p + 1 := by
        simpa [B] using Nat.mul_div_cancel' (Even.two_dvd heven)
      have : 3 ∣ p + 1 := by
        rw [← hsplit]
        exact dvd_mul_of_dvd_right hd 2
      have : (p + 1) % 3 = 0 := (Nat.dvd_iff_mod_eq_zero).1 this
      omega
    have hB : B.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hB0
    have hq0 : ¬ 3 ∣ q := by
      intro hd
      exact hqne3 ((Nat.prime_dvd_prime_iff_eq (by decide : (3 : Nat).Prime) hq).1 hd).symm
    have hr0 : ¬ 3 ∣ r := by
      intro hd
      exact hrne3 ((Nat.prime_dvd_prime_iff_eq (by decide : (3 : Nat).Prime) hr).1 hd).symm
    have hqf : q.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hq0
    have hrf : r.factorization 3 = 0 := Nat.factorization_eq_zero_of_not_dvd hr0
    have hd1 : d1 ≠ 0 := by
      intro h
      have : m ^ 2 = 0 := by simp [hfac, D, h]
      have : m = 0 := by simpa using this
      simp [this] at hm
    have hD : D.factorization 3 = 2 * d1.factorization 3 := by
      simpa [D] using Nat.factorization_pow (n := d1) (k := 2) (p := 3)
    have hposA : A ≠ 0 := by
      have : 0 < A := by
        have := hp.pos
        simp [A]
      exact this.ne'
    have hposB : B ≠ 0 := by
      have hle : 2 ≤ p + 1 := by
        have := hp.two_le
        omega
      have : 0 < B := by
        simpa [B] using Nat.div_pos hle (by decide : 0 < 2)
      exact this.ne'
    have hposC : C ≠ 0 := by
      have : 0 < C := by
        have hp1 : 1 ≤ p := hp.pos
        have hle : p ≤ p ^ 2 := by nlinarith
        simp [C]
      exact this.ne'
    have hposD : D ≠ 0 := by simp [D, pow_ne_zero, hd1]
    have hposq : q ≠ 0 := hq.ne_zero
    have hposr : r ≠ 0 := hr.ne_zero
    have add2 (a b : Nat) (ha : a ≠ 0) (hb : b ≠ 0) :
        (a * b).factorization 3 = a.factorization 3 + b.factorization 3 := by
      rw [Nat.factorization_mul ha hb, Finsupp.add_apply]
    have hsum : (m ^ 2).factorization 3 =
        A.factorization 3 + B.factorization 3 + C.factorization 3 + D.factorization 3
          + q.factorization 3 + r.factorization 3 := by
      rw [hfac]
      have hAB : (A * B).factorization 3 = A.factorization 3 + B.factorization 3 := add2 _ _ hposA hposB
      have hABC : (A * B * C).factorization 3 =
          (A * B).factorization 3 + C.factorization 3 := add2 _ _ (mul_ne_zero hposA hposB) hposC
      have hABCD : (A * B * C * D).factorization 3 =
          (A * B * C).factorization 3 + D.factorization 3 :=
        add2 _ _ (mul_ne_zero (mul_ne_zero hposA hposB) hposC) hposD
      have hABCDQ : (A * B * C * D * q).factorization 3 =
          (A * B * C * D).factorization 3 + q.factorization 3 :=
        add2 _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero hposA hposB) hposC) hposD) hposq
      have hAll : (A * B * C * D * q * r).factorization 3 =
          (A * B * C * D * q).factorization 3 + r.factorization 3 :=
        add2 _ _ (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero hposA hposB) hposC) hposD) hposq) hposr
      omega
    have heven : Even ((m ^ 2).factorization 3) := by
      rw [Nat.factorization_pow]
      exact even_two_mul _
    have hoddval : Odd ((m ^ 2).factorization 3) := by
      rw [hsum, hA, hB, hC, hD, hqf, hrf]
      simpa using (Odd.add_even odd_one (even_two_mul (d1.factorization 3)))
    exfalso
    exact (Nat.not_even_iff_odd.2 hoddval) heven
  · omega
