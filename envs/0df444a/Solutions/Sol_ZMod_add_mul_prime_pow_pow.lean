-- Prove2me | solution 1 for ZMod.add_mul_prime_pow_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:11:16.74028+00:00
-- url     : https://prove2.me/submissions/479cfa31-fef8-45e7-83eb-33ccccefaf74

import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Algebra.Ring.Regular
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.ZMod.Units
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Field.Power
import Definitions.Def_MillerRabin_Lemmas

set_option autoImplicit false
open Nat
open ZMod
namespace ZMod
theorem _root_.solution {p m n : ℕ} (x c : ZMod (p ^ (m + 1))) (hm : 0 < m) (hn : 0 < n) :
    (x + c * p ^ m) ^ n = x ^ n + x ^ (n - 1) * c * p ^ m * n := by
  suffices ((Finset.range (n - 1)).sum fun k ↦
      x ^ k * (c * p ^ m) ^ (n - k) * choose n k) = 0 by
    nth_rw 1 [← show n - 1 + 1 = n by omega]
    rw [add_pow, Finset.sum_range_succ, Finset.sum_range_succ]
    simp [show n - 1 + 1 = n by omega, this, choose_symm hn, show n - (n - 1) = 1 by omega]
    ring
  refine Finset.sum_eq_zero fun k hk ↦ ?_
  rw [Finset.mem_range] at hk
  ring_nf
  rw [show n - k = 2 + (n - 2 - k) by omega, mul_add, pow_add _ (m * 2)]
  suffices (p : ZMod (p ^ (m + 1))) ^ (m * 2) = 0 by
    simp [this]
  rw [ZMod.natCast_pow_eq_zero_of_le]
  omega
end ZMod
