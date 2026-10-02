-- Prove2me | solution 2 for WeakGoldbach.ternary_goldbach_all_odd_9
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-02T09:12:38.62108+00:00
-- url     : https://prove2.me/submissions/b7342281-70a7-4931-88a9-4e822fc216b6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_WeakGoldbach_ternary_goldbach_all_odd_ge_9

set_option maxRecDepth 10000
set_option maxHeartbeats 800000

-- Reduction of `ternary_goldbach_all_odd_9` (e987963c) through the CORRECTED
-- record `ternary_goldbach_all_odd_ge_9` (42fb8198).
--
-- These two statements are literally the same assertion: both take
-- `(n : Nat) (hlo : 9 <= n) (hodd : Odd n)` and conclude the existence of three
-- odd primes summing to `n`. `ternary_goldbach_all_odd_ge_9` is the corrected
-- record, published to replace `ternary_goldbach_all_odd` (4e160e92), whose
-- floor `5 < n` is DISPROVED at `n = 7`.
--
-- Registering this edge retires the duplicate: leaves that referenced the
-- refuted floor-5 record can now be routed through a single non-refuted
-- ancestor, and this duplicate leaf stops being an isolated root with no
-- provenance link to the corrected statement.
--
-- Because the two statements coincide, the proof is a direct application: no
-- arithmetic, no floor transport, and no side condition is required.
open WeakGoldbach

theorem solution (n : Nat) (hlo : 9 <= n) (hodd : Odd n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) :=
  WeakGoldbach.ternary_goldbach_all_odd_ge_9 n hlo hodd
