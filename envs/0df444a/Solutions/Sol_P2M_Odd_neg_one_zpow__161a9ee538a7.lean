-- Prove2me | solution 1 for P2M_Odd_neg_one_zpow__161a9ee538a7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:13:43.663051+00:00
-- url     : https://prove2.me/submissions/2d05f820-8969-44bd-ab99-c3ff9e993fb8

import Mathlib.Algebra.Ring.Int.Parity
import Definitions.Def_MillerRabin_Mathlib_Algebra_Ring_Int_Parity
import Theorems.Thm_P2M_Odd_neg_zpow__2b53500ec918

set_option autoImplicit false
variable {α : Type*}
variable [Group α] [HasDistribNeg α] {n : ℤ}
namespace Odd
theorem _root_.solution (h : Odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_zpow', one_zpow]
end Odd
