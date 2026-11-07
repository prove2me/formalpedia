-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircle_coordinates_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:11.137389+00:00
-- url     : https://prove2.me/submissions/dd33fd2e-a63c-4a09-b16c-eff73bfd7ab2

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatSquare_coordinate_bound

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : ℕ × ℕ) (n R : ℕ)
    (ha : a.1^2+a.2^2=n) (hn : n ≤ R^2) : a.1 ≤ R ∧ a.2 ≤ R := by
  constructor
  · exact lpsNatSquare_coordinate_bound a.1 n R (by omega) hn
  · exact lpsNatSquare_coordinate_bound a.2 n R (by omega) hn
end QEC.Coding.TannerLiftedProduct
