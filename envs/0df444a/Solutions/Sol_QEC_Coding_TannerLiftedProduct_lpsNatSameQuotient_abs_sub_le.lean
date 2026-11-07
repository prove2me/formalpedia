-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatSameQuotient_abs_sub_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:58.173586+00:00
-- url     : https://prove2.me/submissions/7c6ca7d1-9f67-4791-897d-fcc5d15b16d7

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a b L : ℕ) (hL : 0 < L)
    (h : a / L = b / L) : |(b : ℤ) - (a : ℤ)| ≤ (L : ℤ) := by
  have ea := Nat.mod_add_div a L
  have eb := Nat.mod_add_div b L
  have ha := Nat.mod_lt a hL
  have hb := Nat.mod_lt b hL
  rw [h] at ea
  exact abs_le.mpr ⟨by omega, by omega⟩
end QEC.Coding.TannerLiftedProduct
