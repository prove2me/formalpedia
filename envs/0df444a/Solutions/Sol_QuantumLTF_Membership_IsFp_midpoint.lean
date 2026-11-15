-- Prove2me | solution 1 for QuantumLTF.Membership.IsFp.midpoint
-- status  : ACCEPTED   (prove)
-- author  : @stockfish-soup
-- created : 2026-11-15T03:40:22.964302+00:00
-- url     : https://prove2.me/submissions/d87db5a8-95fa-4270-a3c5-177cb44a5554

import Mathlib
import Definitions.Def_QuantumLTF_Membership_IsFp

open QuantumLTF.Membership

theorem solution (B f : ℕ) (x y : ℝ)
    (hx : IsFp B f x) (hy : IsFp B f y) :
    IsFp (B + 1) (f + 1) ((x + y) / 2) := by
  rcases hx with ⟨hfb, k, hk, rfl⟩
  rcases hy with ⟨_, l, hl, rfl⟩
  refine ⟨Nat.add_le_add_right hfb 1, k + l, ?_, ?_⟩
  · have habs : |k + l| ≤ |k| + |l| := abs_add_le k l
    have hsum : |k| + |l| < (2 : ℤ) ^ B + (2 : ℤ) ^ B := add_lt_add hk hl
    calc
      |k + l| ≤ |k| + |l| := habs
      _ < (2 : ℤ) ^ B + (2 : ℤ) ^ B := hsum
      _ = (2 : ℤ) ^ (B + 1) := by rw [pow_succ]; ring
  · push_cast
    rw [pow_succ]
    ring
