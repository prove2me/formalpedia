-- Prove2me | solution 2 for WeakGoldbach.prime_in_4e18_window_4e18_to_1e26
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-09T23:23:30.919185+00:00
-- url     : https://prove2.me/submissions/0288bb0f-0876-4bff-b3cd-1ea93cd3b6ac

import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Tactic.NormNum
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp01
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp02
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp03
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp04
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp05
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp06
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp07
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp08
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp09
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp10
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp11
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp12
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp13
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp14
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp15
import Theorems.Thm_WeakGoldbach_prime_in_4e18_window_proth_grp16

/-! Reduction of `WeakGoldbach.prime_in_4e18_window_4e18_to_1e26` (f83fa300) to the 16 Proth ladder blocks `WeakGoldbach.prime_in_4e18_window_proth_grp01` .. `WeakGoldbach.prime_in_4e18_window_proth_grp16`. Block `k` gives a prime in `(x, x + 4 * 10 ^ 18)` for `A_k ≤ x < B_k`, with `A_1 = 3999671458128199681 ≤ 4 * 10 ^ 18`, `A_{k+1} = B_k` and `B_16 = 100000000351847213166493697 > 10 ^ 26`. A balanced case split on `x` over the boundaries puts every `x ∈ [4 * 10 ^ 18, 10 ^ 26]` into exactly one block. -/

theorem solution (x : ℕ)
    (hxl : 4 * 10 ^ 18 ≤ x) (hx : x ≤ 10 ^ 26) :
    ∃ p : ℕ, x < p ∧ p < x + 4 * 10 ^ 18 ∧ Nat.Prime p := by
  have e1 : (4 : ℕ) * 10 ^ 18 = 4000000000000000000 := by norm_num
  have e2 : (10 : ℕ) ^ 26 = 100000000000000000000000000 := by norm_num
  rw [e1] at hxl
  rw [e2] at hx
  rcases Nat.lt_or_ge x 50127879408826535316029441 with hc8 | hc8
  · rcases Nat.lt_or_ge x 25063941703624474117537793 with hc4 | hc4
    · rcases Nat.lt_or_ge x 12531972851867868448423937 with hc2 | hc2
      · rcases Nat.lt_or_ge x 6265988425752071102267393 with hc1 | hc1
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp01 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp02 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 18797957278071626724802561 with hc3 | hc3
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp03 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp04 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 37595910556489387507449857 with hc6 | hc6
      · rcases Nat.lt_or_ge x 31329926130109707370627073 with hc5 | hc5
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp05 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp06 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 43861894982745922341961729 with hc7 | hc7
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp07 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp08 x (by omega) (by omega)
  · rcases Nat.lt_or_ge x 75191817113483238747144193 with hc12 | hc12
    · rcases Nat.lt_or_ge x 62659848260934984706031617 with hc10 | hc10
      · rcases Nat.lt_or_ge x 56393863834836779545919489 with hc9 | hc9
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp09 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp10 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 68925832687279480470765569 with hc11 | hc11
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp11 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp12 x (by omega) (by omega)
    · rcases Nat.lt_or_ge x 87723785965626872509235201 with hc14 | hc14
      · rcases Nat.lt_or_ge x 81457801538138884651614209 with hc13 | hc13
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp13 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp14 x (by omega) (by omega)
      · rcases Nat.lt_or_ge x 93861893158763431116931073 with hc15 | hc15
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp15 x (by omega) (by omega)
        · exact WeakGoldbach.prime_in_4e18_window_proth_grp16 x (by omega) (by omega)
