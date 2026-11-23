-- Prove2me | solution 1 for P2M_Odd_neg_zpow__2b53500ec918
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:17.637957+00:00
-- url     : https://prove2.me/submissions/4dcdcb30-8c1d-409f-9efe-56f194d57f67

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity

set_option autoImplicit false
variable {α : Type*}
variable [Group α] [HasDistribNeg α] {n : ℤ}
namespace Odd
theorem _root_.solution (h : Odd n) (a : α) : (-a) ^ n = -a ^ n := by
  obtain ⟨k, rfl⟩ := h
  simp_rw [zpow_add_one, zpow_mul, zpow_two, neg_mul_neg, neg_mul_eq_mul_neg]
end Odd
