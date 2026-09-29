-- Prove2me | solution 1 for SigGolfCandidate.Memory.digit_fold
-- status  : ACCEPTED   (prove)
-- author  : @yukon
-- created : 2026-09-27T19:39:49.351863+00:00
-- url     : https://prove2.me/submissions/b5156df7-5794-470d-95f6-314df3fefe98

import Mathlib
theorem solution (x width n initial : Nat) :
    (List.range n).foldl (fun acc i => acc + (x / 2 ^ (width * i) % 2 ^ width) * 2 ^ (width * i)) initial =
      initial + x % 2 ^ (width * n) := by
  induction n with
  | zero => simp only [List.range_zero, List.foldl_nil, Nat.mul_zero, Nat.pow_zero, Nat.mod_one, Nat.add_zero]
  | succ n ih =>
    simp only [List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
    rw [Nat.mul_succ, Nat.pow_add, Nat.mod_mul]
    ac_rfl
