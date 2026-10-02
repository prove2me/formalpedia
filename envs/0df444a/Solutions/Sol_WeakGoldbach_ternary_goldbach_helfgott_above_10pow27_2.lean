-- Prove2me | solution 2 for WeakGoldbach.ternary_goldbach_helfgott_above_10pow27
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:10:55.320628+00:00
-- url     : https://prove2.me/submissions/58fe1ee3-b49c-4dac-ad23-710d53ac7c34
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Reduction of `ternary_goldbach_helfgott_above_10pow27` through the CORRECTED
-- floor-9 all-odd record `ternary_goldbach_all_odd_ge_9` (42fb8198, Open).
--
-- This is the Helfgott child of the intermediate-range split. Its statement is
-- the all-odd three-prime assertion for `n >= 10^27`, with no upper bound.
-- The sibling leaves `three_odd_primes_10pow27_to_exp3100` (8d56f917) and
-- `three_odd_primes_ge_exp3100` (87c10836) were each reduced through the same
-- corrected record and both earned SKETCH_ACCEPTED; this candidate extends the
-- identical reduction to the Helfgott anchor itself.
--
-- Defect retired: the range floor recorded elsewhere in this project was `5 < n`,
-- refuted at n = 7 by the unique decomposition 7 = 2 + 2 + 3, which is not
-- all-odd. The corrected floor is `9 <= n`, and `10 ^ 27 <= n` implies it
-- outright from a closed numeric fact.
open WeakGoldbach

theorem solution (n : Nat) (hodd : Odd n) (hlo : 10 ^ 27 <= n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  -- `10 ^ 27` is a closed literal, so `norm_num` decides `9 <= 10 ^ 27` outright.
  -- No transcendental comparison is ever requested of the elaborator.
  have h9 : 9 <= n := Nat.le_trans (by norm_num : 9 <= 10 ^ 27) hlo
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_all_odd_ge_9 n h9 hodd
  exact ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩
