-- Prove2me | solution 2 for WeakGoldbach.ternary_goldbach_intermediate_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:10:55.440359+00:00
-- url     : https://prove2.me/submissions/55b8c1db-31ce-4999-bb20-4ead15dbe39f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Reduction of `ternary_goldbach_intermediate_range` through the CORRECTED
-- floor-9 all-odd record `ternary_goldbach_all_odd_ge_9` (42fb8198, Open).
--
-- The intermediate range `10^27 <= n < exp 3100`. The floor-9 child places no
-- upper restriction on `n`, so the target's lower hypothesis `10 ^ 27 <= n`
-- alone discharges it and `hhi` is unused.
--
-- Defect retired: the floor `5 < n` used elsewhere in this project is refuted at
-- n = 7 (unique decomposition 7 = 2 + 2 + 3, not all-odd). The corrected floor
-- `9 <= n` follows from `10 ^ 27 <= n` by a closed numeric comparison.
open WeakGoldbach

theorem solution (n : Nat) (hodd : Odd n) (hlo : 10 ^ 27 <= n) (hhi : (n : Real) < Real.exp 3100) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  have h9 : 9 <= n := Nat.le_trans (by norm_num : 9 <= 10 ^ 27) hlo
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    WeakGoldbach.ternary_goldbach_all_odd_ge_9 n h9 hodd
  exact ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩
