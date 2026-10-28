-- Prove2me | solution 1 for WeakGoldbach.helfgott_platt_block_ladders_grp01
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-21T05:20:37.52166+00:00
-- url     : https://prove2.me/submissions/be27429c-34b6-4dfa-8ad9-0ef8aa36dec7
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg01
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg02
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg03
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg04
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg05
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg06
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg07
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg08
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg09
import Theorems.Thm_WeakGoldbach_helfgott_platt_block_ladders_grp01_sg10

set_option autoImplicit false

theorem solution (b : ℕ) (hb : b < 49270) :
    ∃ (k : ℕ) (p : ℕ → ℕ),
      (∀ i, i ≤ k → Nat.Prime (p i)) ∧
      (b*18014398509481984000000000 < p 0 ∧
        p 0 ≤ b*18014398509481984000000000 + 2*10^18) ∧
      (∀ i, i < k → p i < p (i+1) ∧ p (i+1) < p i + 4*10^18) ∧
      (p k ≤ (b+1)*18014398509481984000000000 ∧
        (b+1)*18014398509481984000000000 < p k + 2*10^18) := by
  rcases Nat.lt_or_ge b 24635 with h5 | h5
  · -- b < 24635
    rcases Nat.lt_or_ge b 9854 with h2 | h2
    · -- b < 9854
      rcases Nat.lt_or_ge b 4927 with h1 | h1
      · -- b < 4927
        exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg01 b (by omega)
      · -- 4927 ≤ b
        exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg02 b (by omega) (by omega)
    · -- 9854 ≤ b
      rcases Nat.lt_or_ge b 14781 with h3 | h3
      · -- b < 14781
        exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg03 b (by omega) (by omega)
      · -- 14781 ≤ b
        rcases Nat.lt_or_ge b 19708 with h4 | h4
        · -- b < 19708
          exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg04 b (by omega) (by omega)
        · -- 19708 ≤ b
          exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg05 b (by omega) (by omega)
  · -- 24635 ≤ b
    rcases Nat.lt_or_ge b 34489 with h7 | h7
    · -- b < 34489
      rcases Nat.lt_or_ge b 29562 with h6 | h6
      · -- b < 29562
        exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg06 b (by omega) (by omega)
      · -- 29562 ≤ b
        exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg07 b (by omega) (by omega)
    · -- 34489 ≤ b
      rcases Nat.lt_or_ge b 39416 with h8 | h8
      · -- b < 39416
        exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg08 b (by omega) (by omega)
      · -- 39416 ≤ b
        rcases Nat.lt_or_ge b 44343 with h9 | h9
        · -- b < 44343
          exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg09 b (by omega) (by omega)
        · -- 44343 ≤ b
          exact WeakGoldbach.helfgott_platt_block_ladders_grp01_sg10 b (by omega) (by omega)
