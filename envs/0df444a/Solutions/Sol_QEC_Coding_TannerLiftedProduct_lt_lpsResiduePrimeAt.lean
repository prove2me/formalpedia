-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lt_lpsResiduePrimeAt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:09.227574+00:00
-- url     : https://prove2.me/submissions/f713fd1f-2169-4875-b90b-2aaa5012c678

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
    {p : ℕ} (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    B < (lpsResiduePrimeAt hp hp4 B).q := by
  exact lt_of_le_of_lt (Nat.le_max_left _ _) (lpsLeastPrimeAbove_spec hp B).1
end QEC.Coding.TannerLiftedProduct
