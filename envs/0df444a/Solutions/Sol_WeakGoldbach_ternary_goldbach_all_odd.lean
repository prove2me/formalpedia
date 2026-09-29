-- Prove2me | solution 1 for WeakGoldbach.ternary_goldbach_all_odd
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-25T13:54:58.953576+00:00
-- url     : https://prove2.me/submissions/ed79063f-270c-4367-91d8-fc554ca3c4ca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_WeakGoldbach_ternary_goldbach_small_range
import Theorems.Thm_WeakGoldbach_ternary_goldbach_intermediate_range
import Theorems.Thm_WeakGoldbach_ternary_goldbach_large_range
import Mathlib

theorem solution (n : Nat) (hgt : 5 < n) (hodd : Odd n) :
    Exists fun p : Nat => Exists fun q : Nat => Exists fun r : Nat =>
      And (Nat.Prime p) (And (Nat.Prime q) (And (Nat.Prime r)
        (And (Odd p) (And (Odd q) (And (Odd r) (n = p + q + r)))))) := by
  by_cases hsmall : n < 10 ^ 27
  · exact WeakGoldbach.ternary_goldbach_small_range n hgt hodd hsmall
  · by_cases hmiddle : (n : Real) < Real.exp 3100
    · have hlo : 10 ^ 27 <= n := Nat.le_of_not_gt hsmall
      exact WeakGoldbach.ternary_goldbach_intermediate_range n hodd hlo hmiddle
    · have hlo : Real.exp 3100 <= (n : Real) := le_of_not_gt hmiddle
      exact WeakGoldbach.ternary_goldbach_large_range n hodd hlo