-- Prove2me | solution 2 for TaoFivePrimes.goldbach_blocks_tile_range
-- status  : ACCEPTED   (prove)
-- author  : @junyihjy
-- created : 2026-09-23T16:34:12.469319+00:00
-- url     : https://prove2.me/submissions/01b4591c-cb7c-45ef-b09e-60ded80dad66

import Mathlib

set_option autoImplicit false

theorem solution (n : ℕ) (hlo : 4 ≤ n) (hhi : n ≤ 4 * 10 ^ 14) :
    ∃ b : ℕ, b < 400000001 ∧
      max 4 (b * 1000000) ≤ n ∧ n ≤ min (4 * 10 ^ 14) ((b + 1) * 1000000 - 1) := by
  refine ⟨n / 1000000, ?_, ?_, ?_⟩
  · -- b < 400000001, from n ≤ 4 * 10^14
    have h1 : n / 1000000 ≤ (4 * 10 ^ 14) / 1000000 := Nat.div_le_div_right hhi
    have h2 : (4 * 10 ^ 14) / 1000000 = 400000000 := by norm_num
    omega
  · -- max 4 (b * 1000000) ≤ n, from 4 ≤ n and (n/1000000) * 1000000 ≤ n
    apply max_le_iff.mpr
    exact ⟨hlo, Nat.div_mul_le_self _ _⟩
  · -- n ≤ min (4*10^14) ((b+1)*1000000 - 1)
    apply le_min_iff.mpr
    refine ⟨hhi, ?_⟩
    have hmod : 1000000 * (n / 1000000) + n % 1000000 = n := Nat.div_add_mod _ _
    have hlt : n % 1000000 < 1000000 := Nat.mod_lt _ (by norm_num)
    omega
