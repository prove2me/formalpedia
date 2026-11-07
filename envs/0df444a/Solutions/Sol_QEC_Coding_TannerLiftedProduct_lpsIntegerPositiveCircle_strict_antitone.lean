-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerPositiveCircle_strict_antitone
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:53:48.968037+00:00
-- url     : https://prove2.me/submissions/51cf9a56-3003-43da-891c-639a97a5441a

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (x y x' y' n : ℤ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hx' : 0 ≤ x') (hy' : 0 ≤ y')
    (h : x^2+y^2=n) (h' : x'^2+y'^2=n) (hxx : x<x') : y'<y := by
  have hxx' : x^2 < x'^2 := (sq_lt_sq₀ hx hx').2 hxx
  have hyy : y'^2 < y^2 := by nlinarith [h,h']
  exact (sq_lt_sq₀ hy' hy).1 hyy
end QEC.Coding.TannerLiftedProduct
