-- Prove2me | solution 1 for P2M_Odd_neg_one_zpow__377cb1c9a7a0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:51.830253+00:00
-- url     : https://prove2.me/submissions/a5181d3b-435b-4d1a-9bc4-c4f5b945db29

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
import Theorems.Thm_P2M_Odd_neg_zpow__d07fa6a13b75

set_option autoImplicit false
variable {α : Type*}
variable [GroupWithZero α] [HasDistribNeg α] {n : ℤ}
namespace Odd
theorem _root_.solution (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow₀, one_zpow]
end Odd
