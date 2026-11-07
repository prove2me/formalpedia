-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatSquare_coordinate_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:49:48.927726+00:00
-- url     : https://prove2.me/submissions/4d4b303d-3b31-4221-a15d-e9f16ee7a9e6

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (x n R : ℕ) (hx : x^2 ≤ n) (hn : n ≤ R^2) : x ≤ R := by
  exact (Nat.pow_le_pow_iff_left (by decide : 2 ≠ 0)).mp (hx.trans hn)
end QEC.Coding.TannerLiftedProduct
