-- Prove2me | solution 2 for WeakGoldbach.ternary_goldbach_large_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:11:44.933824+00:00
-- url     : https://prove2.me/submissions/66963b47-b31e-49c6-96b7-cc3414008e24
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Reduction of `ternary_goldbach_large_range` through the CORRECTED floor-9
-- all-odd record `ternary_goldbach_all_odd_ge_9` (42fb8198, Open).
--
-- The asymptotic anchor `exp 3100 <= n`. The floor-9 child has no upper bound
-- and no lower bound beyond `9 <= n`, so the only work is showing the target's
-- transcendental lower hypothesis implies `9 <= n`.
--
-- That step is entirely rational: `Real.exp 3100 >= 1` because `1 <= exp 0`
-- (`Real.add_zero_le_exp`) and `0 < 3100` makes `exp` increasing, so
-- `exp 3100 >= 1 > 9` is false -- the correct reading is `exp 3100 >= 9`
-- directly, using `exp x >= 1 + x` and `1 + 3100 >= 9`.
open WeakGoldbach

theorem solution (n : Nat) (hodd : Odd n) (hlo : Real.exp 3100 <= (n : Real)) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  -- `1 + 3100 >= 9` is closed rational arithmetic, so `Real.add_one_le_exp 3100`
  -- already gives `exp 3100 >= 9` with no further normalisation needed.
  have hexp : (9 : Real) <= Real.exp 3100 := by
    have h := Real.add_one_le_exp 3100
    linarith
  have h9 : 9 <= n := Nat.le_trans (Nat.cast_le.mp (hexp.trans hlo)) (by norm_num)
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_all_odd_ge_9 n h9 hodd
  exact ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩
