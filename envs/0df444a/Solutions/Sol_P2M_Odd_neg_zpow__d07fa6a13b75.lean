-- Prove2me | solution 1 for P2M_Odd_neg_zpow__d07fa6a13b75
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:12:59.164906+00:00
-- url     : https://prove2.me/submissions/3d5fc388-8a2c-4a0a-82d0-29de917c0d84

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity

set_option autoImplicit false
variable {α : Type*}
variable [GroupWithZero α] [HasDistribNeg α] {n : ℤ}
namespace Odd
theorem _root_.solution (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  have hn : n ≠ 0 := by rintro rfl; exact Int.not_even_iff_odd.2 h Even.zero
  obtain ⟨k, rfl⟩ := h
  simp_rw [zpow_add' (.inr (.inl hn)), zpow_one, zpow_mul, zpow_two, neg_mul_neg,
    neg_mul_eq_mul_neg]
end Odd
