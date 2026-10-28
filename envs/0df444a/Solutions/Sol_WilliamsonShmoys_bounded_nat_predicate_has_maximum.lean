-- Prove2me | solution 1 for WilliamsonShmoys.bounded_nat_predicate_has_maximum
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-27T05:37:27.133265+00:00
-- url     : https://prove2.me/submissions/241c4f5d-f61f-42a0-a6ea-418154f92974

import Mathlib
theorem solution (P : Nat → Prop) (hP : ∃ n, P n) (B : Nat) (hB : ∀ n, P n → n ≤ B) : ∃ m, P m ∧ ∀ n, P n → n ≤ m := by
  classical
  obtain ⟨n0, hn0⟩ := hP
  refine ⟨Nat.findGreatest P B, Nat.findGreatest_spec (hB n0 hn0) hn0, fun n hn => Nat.le_findGreatest (hB n hn) hn⟩
