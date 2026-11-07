-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsNatCircleBoxRank_eq_imp_quotients_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:55:59.513942+00:00
-- url     : https://prove2.me/submissions/6ed7a68d-200b-4b8e-9386-943d6c90e323

import Definitions.Def_QEC_Coding_ExpanderCodes_LPSTraceQuadraticForm
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSIntegerThreeSquareCount
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_lpsNatCircle_y_antitone

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
noncomputable section
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution (a b : ℕ × ℕ) (n M L : ℕ)
    (ha : a.1^2+a.2^2=n) (hb : b.1^2+b.2^2=n)
    (haB : a.1/L ≤ M ∧ a.2/L ≤ M) (hbB : b.1/L ≤ M ∧ b.2/L ≤ M)
    (h : lpsNatCircleBoxRank M L a = lpsNatCircleBoxRank M L b) :
    a.1/L=b.1/L ∧ a.2/L=b.2/L := by
  unfold lpsNatCircleBoxRank at h
  rcases le_total a.1 b.1 with hab | hba
  · have hx : a.1/L ≤ b.1/L := Nat.div_le_div_right hab
    have hy : b.2/L ≤ a.2/L := Nat.div_le_div_right (lpsNatCircle_y_antitone a b n ha hb hab)
    constructor <;> omega
  · have hx : b.1/L ≤ a.1/L := Nat.div_le_div_right hba
    have hy : a.2/L ≤ b.2/L := Nat.div_le_div_right (lpsNatCircle_y_antitone b a n hb ha hba)
    constructor <;> omega
end QEC.Coding.TannerLiftedProduct
