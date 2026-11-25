-- Prove2me | solution 1 for collatz_coalescence_residual_fifteen_mod_sixteen_after_trailing_ones_certificates
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Jie Luo
-- created : 2026-11-25T18:28:54.593921+00:00
-- url     : https://prove2.me/submissions/583a7b88-c183-441f-8021-c91d6bb5b2c1
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_two_odd_run_smaller_coalescence
import Theorems.Thm_collatz_coalescence_residual_fifteen_mod_sixteen_after_two_odd_run_certificates

theorem solution (n : ℕ)
    (hlarge : 2310000 ≤ n) (hclass : n % 16 = 15)
    (hmod9 : n % 9 = 0 ∨ n % 9 = 1 ∨ n % 9 = 3 ∨ n % 9 = 6 ∨ n % 9 = 7)
    (hpreimage : ∀ t : ℕ, t ≤ 128 → n ≤ collatzMinPreimage 16 (collatzStep^[t] n))
    (h81 : n % 81 ≠ 10)
    (h2304 : n % 2304 ≠ 1743 ∧ n % 2304 ≠ 1599)
    (h4608 : n % 4608 ≠ 2847 ∧ n % 4608 ≠ 735 ∧ n % 4608 ≠ 991 ∧
      n % 4608 ≠ 2527 ∧ n % 4608 ≠ 3039 ∧ n % 4608 ≠ 4575)
    (h2187 : n % 2187 ∉ [205, 325, 919, 991, 1000, 1090, 1171, 2170])
    (h19683 : n % 19683 ∉ ([154, 433, 1384, 1663, 2134, 2548, 3268, 3364,
      3970, 4249, 4498, 4816, 5671, 5815, 6382, 6517,
      6805, 7516, 8227, 8650, 9352, 11053, 11197, 12187,
      12898, 13312, 14032, 15013, 15580, 17146, 17281, 18376] : List ℕ))
    (hfirst : let L := (n+1).factorization 2
      let q := (n+1)/2^L
      let P := 3^L*q
      ¬ (P % 4 = 1 ∨
      P % 256 ∈ ([43] : List ℕ) ∨
      P % 512 ∈ ([199, 363] : List ℕ) ∨
      P % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
      P % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
      P % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
      P % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ) ∨
      (P % 4 = 3 ∧ ∃ s : ℕ, 2 ≤ s ∧ 2^s ∣ 3*P-1 ∧ 3*3^L+2^s ≤ 2^(L+s)))) :
    ∃ k a b : ℕ, 0 < k ∧ k < n ∧ collatzStep^[a] n = collatzStep^[b] k := by
  let L := (n+1).factorization 2
  let q := (n+1)/2^L
  let X := (3^L*q-1)/2
  let H := (X+1).factorization 2
  let Q := (X+1)/2^H
  let W := 3^H*Q
  have hsplit : 2^L*q = n+1 := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hsplitNext : 2^H*Q = X+1 := Nat.ordProj_mul_ordCompl_eq_self _ _
  have hL : 4 ≤ L := by
    apply (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two (Nat.succ_ne_zero n)).mp
    apply Nat.dvd_iff_mod_eq_zero.mpr
    change (n+1)%16 = 0
    omega
  have hq : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro zeroQ
    rw [zeroQ,mul_zero] at hsplit
    exact (Nat.succ_ne_zero n) hsplit.symm
  have hQ : 0 < Q := by
    apply Nat.pos_of_ne_zero
    intro zeroQ
    rw [zeroQ,mul_zero] at hsplitNext
    exact (Nat.succ_ne_zero X) hsplitNext.symm
  have hqOdd : q%2=1 := by
    have hnd : ¬ 2 ∣ q := Nat.not_dvd_ordCompl Nat.prime_two (Nat.succ_ne_zero n)
    rw [Nat.dvd_iff_mod_eq_zero] at hnd
    omega
  have hPodd : (3^L*q)%2 = 1 := by
    rw [Nat.mul_mod,Nat.pow_mod,show (3:ℕ)%2=1 by decide,one_pow,hqOdd]
    decide
  have hbetween : 3^L*q+1 = 2^(H+1)*Q := by
    have hraw : 3^L*q+1 = 2*(X+1) := by dsimp [X]; omega
    rw [hraw, ← hsplitNext, pow_succ]
    exact Nat.mul_left_comm 2 (2^H) Q |>.trans (Nat.mul_assoc _ _ _).symm
  have hn : 2^L*q-1 = n := by omega
  by_cases hc : (L ≤ 4 ∧ 3 ≤ H ∧
        (W % 256 ∈ ([43] : List ℕ) ∨
        W % 512 ∈ ([199, 363] : List ℕ) ∨
        W % 1024 ∈ ([235, 395, 583] : List ℕ) ∨
        W % 2048 ∈ ([263, 795, 839, 1163, 1175, 1515] : List ℕ) ∨
        W % 4096 ∈ ([523, 631, 775, 1003, 1675, 1687, 1895, 2331, 2351, 2375] : List ℕ) ∨
        W % 8192 ∈ ([1051, 1263, 1547, 3079, 3355, 3375, 3399, 3787, 3847, 3991, 4699, 4747, 4759, 5207, 6123, 7015, 7799] : List ℕ))) ∨
      (L ≤ 7 ∧ 5 ≤ H ∧
        (W % 16384 ∈ ([303, 2731, 6371] : List ℕ) ∨
        W % 32768 ∈ ([12715, 18659, 20783, 23211] : List ℕ) ∨
        W % 65536 ∈ ([1131, 8419, 15019, 25259, 26851, 30339, 37291, 39215, 45359, 47275, 60263] : List ℕ))) ∨
      (L ≤ 12 ∧ 7 ≤ H ∧
        (W % 262144 ∈ ([4551, 43691, 198427, 208743] : List ℕ))) ∨
      (∃ s : ℕ, 2^s ∣ W-1 ∧ W ≤ 2^s*(n))
  · have h := collatz_two_odd_run_smaller_coalescence L q H Q hL hq hQ hbetween (by simpa only [hn] using hc)
    rw [hn] at h
    exact h
  · exact collatz_coalescence_residual_fifteen_mod_sixteen_after_two_odd_run_certificates
      n hlarge hclass hmod9 hpreimage h81 h2304 h4608 h2187 h19683 hfirst hc
