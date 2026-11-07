-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSResiduePrime.two_mul_card_psl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:32:03.767474+00:00
-- url     : https://prove2.me/submissions/a357a527-2627-4d04-be4b-8ea1b1581dd6

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_sl_two_zmod
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_center_sl_two_zmod

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
namespace QEC.Coding.TannerLiftedProduct
namespace LPSResiduePrime
theorem _root_.solution (a : LPSResiduePrime p) :
    2 * Fintype.card PSL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) := by
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center SL(2, ZMod a.q))
  change Nat.card SL(2, ZMod a.q) =
    Nat.card PSL(2, ZMod a.q) *
      Nat.card (Subgroup.center SL(2, ZMod a.q)) at hquot
  have hsl : Nat.card SL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) := by
    rw [Nat.card_eq_fintype_card, card_sl_two_zmod]
  have hqTwo : a.q ≠ 2 := by
    have hmod := a.modFour
    omega
  rw [hsl, card_center_sl_two_zmod a.q hqTwo] at hquot
  rw [Nat.card_eq_fintype_card] at hquot
  omega
end LPSResiduePrime
end QEC.Coding.TannerLiftedProduct
