-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_psl_two_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:32:00.468629+00:00
-- url     : https://prove2.me/submissions/61e9b297-af5b-48c4-abc1-6471517c8c19

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
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    Fintype.card PSL(2, ZMod q) = q * (q ^ 2 - 1) / 2 := by
  have hquot := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (Subgroup.center SL(2, ZMod q))
  change Nat.card SL(2, ZMod q) =
    Nat.card PSL(2, ZMod q) *
      Nat.card (Subgroup.center SL(2, ZMod q)) at hquot
  have hsl : Nat.card SL(2, ZMod q) = q * (q ^ 2 - 1) := by
    rw [Nat.card_eq_fintype_card, card_sl_two_zmod]
  rw [hsl, card_center_sl_two_zmod q hqTwo] at hquot
  rw [← Nat.card_eq_fintype_card]
  omega
end QEC.Coding.TannerLiftedProduct
