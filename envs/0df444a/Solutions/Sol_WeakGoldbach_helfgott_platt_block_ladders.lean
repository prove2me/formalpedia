-- Prove2me | solution 1 for WeakGoldbach.helfgott_platt_block_ladders
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan
-- created : 2026-10-21T05:17:57.214101+00:00
-- url     : https://prove2.me/submissions/79afb9c6-96e8-47ec-9eb9-3b445c00946f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp02
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp03
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp04
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp05
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp06
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp07
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp08
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp09
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp10

set_option autoImplicit false

theorem solution (b : ℕ) (hb : b < 492700) :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      (b*18014398509481984000000000 < p 0 ∧
        p 0 ≤ b*18014398509481984000000000 + 2*10^18) ∧
      (∀ i, i < k → p i < p (i+1) ∧ p (i+1) < p i + 4*10^18) ∧
      (p k ≤ (b+1)*18014398509481984000000000 ∧
        (b+1)*18014398509481984000000000 < p k + 2*10^18) := by
  rcases Nat.lt_or_ge b 246350 with h5 | h5
  · -- b < 246350
    rcases Nat.lt_or_ge b 98540 with h2 | h2
    · -- b < 98540
      rcases Nat.lt_or_ge b 49270 with h1 | h1
      · -- b < 49270
        exact WeakGoldbach.helfgott_platt_block_ladders_grp01 b (by omega)
      · -- 49270 ≤ b
        exact WeakGoldbach.helfgott_platt_block_ladders_grp02 b (by omega) (by omega)
    · -- 98540 ≤ b
      rcases Nat.lt_or_ge b 147810 with h3 | h3
      · -- b < 147810
        exact WeakGoldbach.helfgott_platt_block_ladders_grp03 b (by omega) (by omega)
      · -- 147810 ≤ b
        rcases Nat.lt_or_ge b 197080 with h4 | h4
        · -- b < 197080
          exact WeakGoldbach.helfgott_platt_block_ladders_grp04 b (by omega) (by omega)
        · -- 197080 ≤ b
          exact WeakGoldbach.helfgott_platt_block_ladders_grp05 b (by omega) (by omega)
  · -- 246350 ≤ b
    rcases Nat.lt_or_ge b 344890 with h7 | h7
    · -- b < 344890
      rcases Nat.lt_or_ge b 295620 with h6 | h6
      · -- b < 295620
        exact WeakGoldbach.helfgott_platt_block_ladders_grp06 b (by omega) (by omega)
      · -- 295620 ≤ b
        exact WeakGoldbach.helfgott_platt_block_ladders_grp07 b (by omega) (by omega)
    · -- 344890 ≤ b
      rcases Nat.lt_or_ge b 394160 with h8 | h8
      · -- b < 394160
        exact WeakGoldbach.helfgott_platt_block_ladders_grp08 b (by omega) (by omega)
      · -- 394160 ≤ b
        rcases Nat.lt_or_ge b 443430 with h9 | h9
        · -- b < 443430
          exact WeakGoldbach.helfgott_platt_block_ladders_grp09 b (by omega) (by omega)
        · -- 443430 ≤ b
          exact WeakGoldbach.helfgott_platt_block_ladders_grp10 b (by omega) (by omega)
