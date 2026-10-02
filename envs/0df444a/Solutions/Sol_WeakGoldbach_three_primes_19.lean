-- Prove2me | solution 19 for WeakGoldbach.three_primes
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T02:56:20.148921+00:00
-- url     : https://prove2.me/submissions/b721b094-c129-4096-841c-e53b7facf314
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_three_primes_three
import Theorems.Thm_WeakGoldbach_three_primes_five
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Reduction of `WeakGoldbach.three_primes` to the CORRECTED all-odd ternary
-- record `ternary_goldbach_all_odd_9` (e987963c, Open).
--
-- Why this differs materially from the accepted sketches (c6002/c6004/c6139):
-- those route `n >= 9` through `three_odd_primes_ge_10pow27` /
-- `verified_three_primes_to_8875e30`, and the `ge_10pow27` branch carries a
-- registered edge to `ternary_goldbach_all_odd` (4e160e92), which is
-- DISPROVED. This candidate instead uses the corrected node, whose statement
-- drops the false `5 < n` floor in favour of the true `9 <= n`, so the whole
-- `n >= 9` range is covered by a single child with no Disproved edge.
--
-- The `n = 7` instance is discharged by an explicit witness `2 + 2 + 3`,
-- which the earlier `Nat.Prime (n - 4)` decidable split could not be relied
-- on to produce.
open WeakGoldbach

theorem solution (n : ℕ) (hodd : Odd n) (hn : 1 < n) :
    ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ p ∈ s, Nat.Prime p) ∧ s.sum = n := by
  -- Any triple of primes whose sum is `n` is a witness multiset.
  have key : ∀ p q r : ℕ, Nat.Prime p → Nat.Prime q → Nat.Prime r → p + q + r = n →
      ∃ s : Multiset ℕ, s.card ≤ 3 ∧ (∀ t ∈ s, Nat.Prime t) ∧ s.sum = n := by
    intro p q r hp hq hr hsum
    refine ⟨p ::ₘ q ::ₘ r ::ₘ (0 : Multiset ℕ), by simp, ?_, ?_⟩
    · intro t ht
      rcases Multiset.mem_cons.mp ht with ht | ht
      · exact ht ▸ hp
      · rcases Multiset.mem_cons.mp ht with ht | ht
        · exact ht ▸ hq
        · rcases Multiset.mem_cons.mp ht with ht | ht
          · exact ht ▸ hr
          · exact absurd ht (by simp)
    · simpa only [Multiset.sum_cons, Multiset.sum_zero, add_zero, add_assoc] using hsum
  -- Oddness as the linear equation `n = 2 * k + 1`, which is the shape `omega`
  -- consumes. (The `obtain ⟨k, hk⟩ := hodd` form hides the parity.)
  obtain ⟨k, hk⟩ := Odd.exists_bit1 hodd
  rcases Nat.lt_or_ge n 9 with hsmall | hbig
  · rcases Nat.lt_or_ge n 5 with hlt5 | hge5
    · have hn3 : n = 3 := by omega
      subst hn3
      exact WeakGoldbach.three_primes_three
    · rcases Nat.lt_or_ge n 7 with hlt7 | hge7
      · have hn5 : n = 5 := by omega
        subst hn5
        exact WeakGoldbach.three_primes_five
      · have hn7 : n = 7 := by omega
        subst hn7
        refine ⟨(2 ::ₘ 2 ::ₘ 3 ::ₘ (0 : Multiset ℕ)), by simp, ?_, ?_⟩
        · intro t ht
          rcases Multiset.mem_cons.mp ht with ht | ht
          · exact ht ▸ (by norm_num : Nat.Prime (2 : ℕ))
          · rcases Multiset.mem_cons.mp ht with ht | ht
            · exact ht ▸ (by norm_num : Nat.Prime (2 : ℕ))
            · rcases Multiset.mem_cons.mp ht with ht | ht
              · exact ht ▸ (by norm_num : Nat.Prime (3 : ℕ))
              · exact absurd ht (by simp)
        · norm_num
  · obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
      WeakGoldbach.ternary_goldbach_all_odd_9 n hbig hodd
    -- Repair of candidate 6196 (CE: APPLICATION TYPE MISMATCH at L67).
    -- `ternary_goldbach_all_odd_9` concludes `n = p + q + r`, while `key`
    -- expects `p + q + r = n`. The compiler reported
    --   Actual type:   n = p + q + r
    --   Expected type: p + q + r = n
    -- so the supplied term is correct and the *expected* orientation is the one
    -- to adapt. `hsum.symm` is the narrowest adapter: it flips only the
    -- equality and leaves every hypothesis untouched.
    exact key p q r hp hq hr hsum.symm

