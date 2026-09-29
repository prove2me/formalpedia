-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_intermediate_range
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T14:09:54.23052+00:00
-- url     : https://prove2.me/submissions/50506cc1-f66b-4561-82cb-9d10d94b64cd
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_ternary_goldbach_helfgott_above_10pow27
import Mathlib

theorem solution (n : Nat) (hodd : Odd n)
    (hlo : 10 ^ 27 <= n) (hhi : (n : Real) < Real.exp 3100) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  exact WeakGoldbach.ternary_goldbach_helfgott_above_10pow27 n hodd hlo
