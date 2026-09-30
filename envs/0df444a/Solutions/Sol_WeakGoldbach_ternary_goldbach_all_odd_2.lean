-- Prove2me | solution 2 for WeakGoldbach.ternary_goldbach_all_odd
-- status  : ACCEPTED   (disprove)
-- author  : @WillR
-- created : 2026-09-30T08:41:02.505966+00:00
-- url     : https://prove2.me/submissions/3e4e4ff1-8ddc-4ce1-b728-0f179572cab9

import Mathlib

theorem solution : ¬ (∀ n : Nat, 5 < n → Odd n →
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r))))))) := by
  intro hall
  obtain ⟨p, q, r, hp, hq, hr, hop, hoq, hor, hsum⟩ :=
    hall 7 (show 5 < 7 by omega) (show Odd 7 from ⟨3, by omega⟩)
  have hp3 : 3 ≤ p := (Nat.Prime.odd_iff hp).mp hop
  have hq3 : 3 ≤ q := (Nat.Prime.odd_iff hq).mp hoq
  have hr3 : 3 ≤ r := (Nat.Prime.odd_iff hr).mp hor
  omega
