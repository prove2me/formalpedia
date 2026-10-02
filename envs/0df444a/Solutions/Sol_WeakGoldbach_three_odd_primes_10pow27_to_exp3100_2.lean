-- Prove2me | solution 2 for WeakGoldbach.three_odd_primes_10pow27_to_exp3100
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T08:15:35.926648+00:00
-- url     : https://prove2.me/submissions/1c7da975-0320-416c-9c99-da0da1a8fbce
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Reduction of `three_odd_primes_10pow27_to_exp3100` through the CORRECTED
-- floor-9 all-odd record `ternary_goldbach_all_odd_ge_9` (42fb8198, Open).
--
-- Same defect as the sibling leaf `three_odd_primes_ge_exp3100`: this target's
-- only registered decomposition child is `ternary_goldbach_all_odd` (4e160e92),
-- which is DISPROVED and refuted at n = 7. This target's own hypothesis
-- `10 ^ 27 <= n` already implies `9 <= n`, so the refuting value is excluded by
-- the target's own range and the registered edge is semantically wrong rather
-- than merely stale. Importing the non-refuted floor-9 statement retires it.
--
-- The upper bound `hhi` is not needed: the floor-9 child covers every odd
-- `n >= 9` with no upper restriction, so importing it discharges this target
-- on the lower hypothesis alone.
open WeakGoldbach

theorem solution (n : ℕ) (hlo : 10 ^ 27 ≤ n) (hhi : (n : ℝ) < Real.exp 3100)
    (hodd : Odd n) :
    ∃ p q r : ℕ,
      Nat.Prime p ∧ Nat.Prime q ∧ Nat.Prime r ∧
      Odd p ∧ Odd q ∧ Odd r ∧ n = p + q + r := by
  -- `10 ^ 27` is a closed literal, so `norm_num` decides the comparison outright
  -- and no `Real.exp` atom is ever asked to reduce.
  have h9 : 9 ≤ n := Nat.le_trans (by norm_num : 9 ≤ 10 ^ 27) hlo
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_all_odd_ge_9 n h9 hodd
  exact ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩
