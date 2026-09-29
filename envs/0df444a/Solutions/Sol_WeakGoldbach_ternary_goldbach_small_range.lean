-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_small_range
-- status  : ACCEPTED   (disprove)
-- author  : @Eyal1990
-- created : 2026-09-25T21:21:12.437869+00:00
-- url     : https://prove2.me/submissions/675c5f6b-5a5e-46d0-b860-61a0a60f4d81

import Mathlib

theorem solution :
    ¬ (∀ (n : Nat) (hgt : 5 < n) (hodd : Odd n)
        (hsmall : n < 10 ^ 27),
        Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
          And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
            (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r))))))) := by
  intro h
  have h7 := h 7 (by norm_num) (by norm_num) (by norm_num)
  rcases h7 with ⟨p, h7⟩
  rcases h7 with ⟨q, h7⟩
  rcases h7 with ⟨r, h7⟩
  rcases h7 with ⟨hp, h7⟩
  rcases h7 with ⟨hq, h7⟩
  rcases h7 with ⟨hr, h7⟩
  rcases h7 with ⟨hpo, h7⟩
  rcases h7 with ⟨hqo, h7⟩
  rcases h7 with ⟨hro, hsum⟩
  have hpge : 3 ≤ p := hp.odd_iff.mp hpo
  have hqge : 3 ≤ q := hq.odd_iff.mp hqo
  have hrge : 3 ≤ r := hr.odd_iff.mp hro
  omega
