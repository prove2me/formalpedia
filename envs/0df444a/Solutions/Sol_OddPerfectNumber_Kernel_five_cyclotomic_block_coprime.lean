-- Prove2me | solution 1 for OddPerfectNumber.Kernel.five_cyclotomic_block_coprime
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T06:43:09.53682+00:00
-- url     : https://prove2.me/submissions/9781d715-7373-4b12-9674-03bd03f9a00a

import Theorems.Thm_OddPerfectNumber_Kernel_five_cyclotomic_pair_coprime
set_option autoImplicit false
open OddPerfectNumber.Kernel

theorem solution (p : Nat) (hp2 : p != 2) :
    Nat.gcd (p ^ 2 + p + 1) (((p + 1) / 2) * (p ^ 2 - p + 1)) = 1 := by
  have hhalf : Nat.Coprime (p ^ 2 + p + 1) ((p + 1) / 2) := by
    rcases Nat.even_or_odd p with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hdiv : (k+k+1)/2 = k := by omega
      rw [hdiv]
      have he : (k+k)^2+(k+k)+1 = (4*k+2)*k+1 := by ring
      rw [he, Nat.coprime_mul_right_add_left]
      exact Nat.coprime_one_left _
    · have hdiv : (2*k+1+1)/2 = k+1 := by omega
      rw [hdiv]
      have he : (2*k+1)^2+(2*k+1)+1 = (4*k+2)*(k+1)+1 := by ring
      rw [he, Nat.coprime_mul_right_add_left]
      exact Nat.coprime_one_left _
  exact (hhalf.mul_right (five_cyclotomic_pair_coprime p hp2)).gcd_eq_one
