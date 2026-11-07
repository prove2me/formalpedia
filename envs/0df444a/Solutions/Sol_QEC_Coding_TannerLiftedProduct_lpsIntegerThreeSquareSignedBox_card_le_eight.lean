-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsIntegerThreeSquareSignedBox_card_le_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:54:39.054308+00:00
-- url     : https://prove2.me/submissions/7f63b1f8-7b35-476c-840e-1cad7aacde18

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_coeff_lpsTraceThetaSeries
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsResiduePrimeAt_q
attribute [local simp] QEC.Coding.TannerLiftedProduct.coeff_lpsTraceThetaSeries
attribute [local simp] QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q



set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a : (ℕ × ℕ) × ℕ) :
    (lpsIntegerThreeSquareSignedBox a).card ≤ 8 := by
  have hx : ({(a.1.1 : ℤ), -(a.1.1 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have hy : ({(a.1.2 : ℤ), -(a.1.2 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  have hz : ({(a.2 : ℤ), -(a.2 : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_le_two
  unfold lpsIntegerThreeSquareSignedBox
  simp only [Finset.product_eq_sprod, Finset.card_product]
  exact Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
end QEC.Coding.TannerLiftedProduct
