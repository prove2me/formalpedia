-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSResiduePrime.card_psl
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:32:47.652505+00:00
-- url     : https://prove2.me/submissions/75e2b0ad-2ba1-4634-bfcc-e96c928930d1

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_card_psl_two_zmod

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
namespace QEC.Coding.TannerLiftedProduct
namespace LPSResiduePrime
theorem _root_.solution (a : LPSResiduePrime p) :
    Fintype.card PSL(2, ZMod a.q) = a.q * (a.q ^ 2 - 1) / 2 := by
  apply card_psl_two_zmod a.q
  have hmod := a.modFour
  omega
end LPSResiduePrime
end QEC.Coding.TannerLiftedProduct
