-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_cyclotomic_coprime_first_mod_three
-- status  : ACCEPTED   (prove)
-- author  : @os0xcom
-- created : 2026-10-03T15:56:42.902258+00:00
-- url     : https://prove2.me/submissions/c88724bb-a97b-4024-a9e8-11b6b6481a1f

import Mathlib

set_option linter.unusedVariables false

theorem solution (p : Nat) (hp : p.Prime) (_hp2 : p != 2) (hp3 : p % 3 = 1) :
    Nat.gcd (p ^ 2 + p + 1) (((p + 1) / 2) * (p ^ 2 - p + 1)) = 1 ∧
      Nat.gcd (((p + 1) / 2) * (p ^ 2 + p + 1)) (p ^ 2 - p + 1) = 1 := by
  have hpne2 : p ≠ 2 := by
    intro h
    rw [h] at hp3
    have : (2 : Nat) % 3 = 2 := by decide
    omega
  have hnot3 : ¬ 3 ∣ p + 1 := by
    intro h
    have : (p + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    omega
  clear hp3
  have hodd : Odd p := hp.odd_of_ne_two hpne2
  have h2dvd : 2 ∣ p + 1 := by
    rcases hodd with ⟨k, hk⟩
    exact ⟨k + 1, by omega⟩
  have hhalf : 2 * ((p + 1) / 2) = p + 1 := Nat.mul_div_cancel' h2dvd
  have hhalf_dvd : (p + 1) / 2 ∣ p + 1 := ⟨2, by
    rw [Nat.mul_comm]
    exact hhalf.symm⟩
  have hle : p ≤ p ^ 2 := by
    calc
      p = p * 1 := (Nat.mul_one p).symm
      _ ≤ p * p := Nat.mul_le_mul_left p (by omega : (1 : Nat) ≤ p)
      _ = p ^ 2 := by ring
  have hp3le : 3 ≤ p := by
    have := hp.two_le
    omega
  have hCD : p ^ 2 + p + 1 = (p ^ 2 - p + 1) + 2 * p := by
    zify [hle]
    ring
  have hg2p : Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1) ∣ 2 * p := by
    have hleft :
        Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1) ∣ (p ^ 2 - p + 1) + 2 * p := by
      rw [← hCD]
      exact Nat.gcd_dvd_left _ _
    exact (Nat.dvd_add_right (Nat.gcd_dvd_right _ _)).mp hleft
  have hnot2 : ¬ 2 ∣ p ^ 2 + p + 1 := by
    rcases hodd with ⟨k, hk⟩
    rw [hk]
    have hform :
        (2 * k + 1) ^ 2 + (2 * k + 1) + 1 = 2 * (2 * k ^ 2 + 3 * k + 1) + 1 := by ring
    rw [hform]
    intro h
    have hmod (t : Nat) : (2 * t + 1) % 2 = 1 := by omega
    have h0 : (2 * (2 * k ^ 2 + 3 * k + 1) + 1) % 2 = 0 := Nat.mod_eq_zero_of_dvd h
    have h1 := hmod (2 * k ^ 2 + 3 * k + 1)
    omega
  have hcop2 : Nat.Coprime (Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1)) 2 := by
    rw [Nat.coprime_comm]
    refine (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 2)).2 ?_
    intro h2
    exact hnot2 (h2.trans (Nat.gcd_dvd_left _ _))
  have hgp : Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1) ∣ p :=
    (Nat.Coprime.dvd_mul_left hcop2).mp hg2p
  have hC : p ^ 2 + p + 1 = p * (p + 1) + 1 := by ring
  have hcop_pC : Nat.Coprime p (p ^ 2 + p + 1) := by
    rw [hC]
    exact (Nat.coprime_mul_left_add_right p 1 (p + 1)).mpr (Nat.coprime_one_right p)
  have hgcdCD : Nat.gcd (p ^ 2 + p + 1) (p ^ 2 - p + 1) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop_pC hgp (Nat.gcd_dvd_left _ _)
  have hcopCp1 : Nat.Coprime (p + 1) (p ^ 2 + p + 1) := by
    rw [show p ^ 2 + p + 1 = (p + 1) * p + 1 by ring]
    exact (Nat.coprime_mul_left_add_right (p + 1) 1 p).mpr (Nat.coprime_one_right (p + 1))
  have hcopChalf : Nat.Coprime ((p + 1) / 2) (p ^ 2 + p + 1) :=
    hcopCp1.coprime_dvd_left hhalf_dvd
  have hD : p ^ 2 - p + 1 = 3 + (p + 1) * ((p + 1) - 3) := by
    clear hnot3
    have h31 : 3 ≤ p + 1 := by omega
    zify [hle, h31]
    ring
  have hcop3 : Nat.Coprime (p + 1) 3 := by
    rw [Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd (by decide : Nat.Prime 3)).2 hnot3
  have hcopDp1 : Nat.Coprime (p + 1) (p ^ 2 - p + 1) := by
    rw [hD]
    exact (Nat.coprime_add_mul_left_right (p + 1) 3 ((p + 1) - 3)).mpr hcop3
  have hcopDhalf : Nat.Coprime ((p + 1) / 2) (p ^ 2 - p + 1) :=
    hcopDp1.coprime_dvd_left hhalf_dvd
  have hCD' : Nat.Coprime (p ^ 2 + p + 1) (p ^ 2 - p + 1) := by
    rw [Nat.Coprime, hgcdCD]
  refine ⟨?_, ?_⟩
  · rw [← Nat.coprime_iff_gcd_eq_one]
    exact (Nat.coprime_mul_iff_right).2 ⟨hcopChalf.symm, hCD'⟩
  · rw [← Nat.coprime_iff_gcd_eq_one]
    exact (Nat.coprime_mul_iff_left).2 ⟨hcopDhalf, hCD'⟩
