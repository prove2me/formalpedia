-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.card_center_sl_two_zmod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:30:49.079212+00:00
-- url     : https://prove2.me/submissions/1e995120-9696-4028-9b24-3d539f019b30

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
namespace QEC.Coding.TannerLiftedProduct
theorem _root_.solution
    (q : ℕ) [Fact q.Prime] (hqTwo : q ≠ 2) :
    Nat.card (Subgroup.center SL(2, ZMod q)) = 2 := by
  calc
    Nat.card (Subgroup.center SL(2, ZMod q)) =
        Nat.card (rootsOfUnity 2 (ZMod q)) := by
      exact Nat.card_congr
        Matrix.SpecialLinearGroup.center_equiv_rootsOfUnity.toEquiv
    _ = 2 := (IsPrimitiveRoot.neg_one q hqTwo).card_rootsOfUnity
end QEC.Coding.TannerLiftedProduct
