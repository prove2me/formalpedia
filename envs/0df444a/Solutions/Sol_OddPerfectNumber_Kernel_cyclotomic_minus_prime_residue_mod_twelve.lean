-- Prove2me | solution 1 for OddPerfectNumber.Kernel.cyclotomic_minus_prime_residue_mod_twelve
-- status  : ACCEPTED   (disprove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T15:05:21.034906+00:00
-- url     : https://prove2.me/submissions/fa427777-b504-4e89-a6e8-bdc9bb4ae735

import Mathlib

/-! Disproof of 58ee84a9 `OddPerfectNumber.Kernel.cyclotomic_minus_prime_residue_mod_twelve`.

Counterexample `p = 3`, `q = 7`: both are prime, `3 != 2`, `7 != 3`, `7 != 3`, and
`7 ∣ 3^2 - 3 + 1 = 7`. But `7 % 12 = 7 ≠ 1` while `3 ∣ 7 - 1 = 6`, so the claimed
equivalence `(7 % 12 = 1) ↔ (3 ∣ 6)` is `False ↔ True`. -/

theorem solution : ¬ (∀ {p q : Nat} (hp : p.Prime) (hp2 : p != 2)
    (hq : q.Prime) (hq3 : q != 3) (hqp : q != p) (hqd : q ∣ p ^ 2 - p + 1),
    (q % 12 = 1) ↔ (3 ∣ q - 1)) := by
  intro h
  have key := @h 3 7 (by norm_num) (by decide) (by norm_num) (by decide) (by decide) (by norm_num)
  have h7 : (7 : Nat) % 12 = 1 := key.mpr (by norm_num)
  norm_num at h7
