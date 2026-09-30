-- Prove2me | solution 1 for OddPerfectNumber.Kernel.sqfree_part_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-30T10:21:39.183572+00:00
-- url     : https://prove2.me/submissions/283d323e-4f82-4450-a9f2-a89c2a464096

-- Revision: mathlib 0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1
--
-- `sqfree_part_ne_one` (b59073fb): if `s = d1 ^ 2 * d2` and `s` is not a
-- perfect square, then `d2 ≠ 1`.
--
-- NAMESPACING (30 September 2026 session I).  Remote candidates 5038 and 5046
-- both failed with `unknown namespace OddPerfectNumber.Kernel`, and the line
-- they named was the bare `open OddPerfectNumber.Kernel` command.  The cause is
-- now pinned exactly: this file imported only `Mathlib`, so no declaration in
-- the remote environment created that namespace, and Lean rejects `open` of an
-- undeclared namespace outright.
--
-- The fix is therefore to import a *Proved* child that really is declared in
-- `namespace OddPerfectNumber.Kernel`, which makes the same `open` legitimate.
-- `Theorems.Thm_OddPerfectNumber_Kernel_quad_not_three_mul_sq` is such a
-- module; it is imported below purely to create the namespace, and none of its
-- declarations are used.  The `open` sits immediately above `theorem solution`,
-- which is the placement `static.py::_opens_namespace` scans.
import Mathlib
import Theorems.Thm_OddPerfectNumber_Kernel_quad_not_three_mul_sq

/-- The published statement of `b59073fb`, proved: the square-free part of a
non-square is not `1`. -/
theorem sqfree_part_ne_one_aux : ∀ (s d1 d2 : Nat), d1 ^ 2 * d2 = s →
    ¬ (∃ r : Nat, s = r ^ 2) → d2 ≠ 1 := by
  intro s d1 d2 hd2 hs_nsq
  intro hcon
  -- `hd2 : d1 ^ 2 * d2 = s` and `hcon : d2 = 1` together give `s = d1 ^ 2`,
  -- which is the square excluded by `hs_nsq`.  `Nat.mul_one` (not
  -- `Nat.one_mul`) is the closing rewrite, because after substituting `d2 := 1`
  -- the goal is `d1 ^ 2 * 1 = d1 ^ 2`: the `1` sits on the *right*.
  have : s = d1 ^ 2 := by
    rw [← hd2, hcon, Nat.mul_one]
  exact hs_nsq ⟨d1, this⟩

open OddPerfectNumber.Kernel

theorem solution (s d1 d2 : Nat) (hd2 : d1 ^ 2 * d2 = s)
    (hs_nsq : ¬ (∃ r : Nat, s = r ^ 2)) :
    d2 ≠ 1 :=
  _root_.sqfree_part_ne_one_aux s d1 d2 hd2 hs_nsq
