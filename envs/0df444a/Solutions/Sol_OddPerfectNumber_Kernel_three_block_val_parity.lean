-- Prove2me | solution 1 for OddPerfectNumber.Kernel.three_block_val_parity
-- status  : ACCEPTED   (disprove)
-- author  : @os0xcom
-- created : 2026-10-03T15:48:47.541959+00:00
-- url     : https://prove2.me/submissions/b5e99cef-c7a2-4c99-b196-16586d7946bd

import Mathlib

set_option linter.unusedVariables false

theorem solution :
    ¬ (∀ (p : Nat) (_hp : p % 3 = 2),
        Odd (((p + 1) / 2 * (p ^ 2 + p + 1) * (p ^ 2 - p + 1)).factorization 3) ↔
          (p + 1).factorization 3 % 2 = 0) := by
  intro h
  have hiff := h 2 (by decide)
  have hprod : ((2 + 1) / 2 * (2 ^ 2 + 2 + 1) * (2 ^ 2 - 2 + 1)) = 21 := by norm_num
  have hp3 : Nat.Prime 3 := by decide
  have h21 : (21 : Nat) ≠ 0 := by decide
  have hle : 1 ≤ (21).factorization 3 :=
    (Nat.Prime.pow_dvd_iff_le_factorization hp3 h21).mp (by decide : 3 ^ 1 ∣ 21)
  have hnot : ¬ 3 ^ 2 ∣ 21 := by decide
  have hlt : (21).factorization 3 < 2 := by
    by_contra hge
    have : 2 ≤ (21).factorization 3 := Nat.le_of_not_lt hge
    exact hnot ((Nat.Prime.pow_dvd_iff_le_factorization hp3 h21).mpr this)
  have hv : (21).factorization 3 = 1 := by omega
  have hv3 : (3).factorization 3 = 1 := by
    have hle3 : 1 ≤ (3).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization hp3 (by decide : (3 : Nat) ≠ 0)).mp
        (by decide : 3 ^ 1 ∣ 3)
    have hnot3 : ¬ 3 ^ 2 ∣ 3 := by decide
    have hlt3 : (3).factorization 3 < 2 := by
      by_contra hge
      exact hnot3 ((Nat.Prime.pow_dvd_iff_le_factorization hp3 (by decide)).mpr (Nat.le_of_not_lt hge))
    omega
  rw [hprod, hv, hv3] at hiff
  -- Odd 1 ↔ 1 % 2 = 0
  have : ¬ (Odd (1 : Nat) ↔ (1 : Nat) % 2 = 0) := by decide
  exact this hiff
