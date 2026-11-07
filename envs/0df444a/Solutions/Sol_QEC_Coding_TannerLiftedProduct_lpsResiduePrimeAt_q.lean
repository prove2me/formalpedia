-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.lpsResiduePrimeAt_q
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:01.687219+00:00
-- url     : https://prove2.me/submissions/baab4a82-60bf-4b41-80db-c3c2c5cdf195

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
theorem _root_.solution {p : ℕ}
    (hp : p.Prime) (hp4 : p % 4 = 1) (B : ℕ) :
    (lpsResiduePrimeAt hp hp4 B).q = lpsLeastPrimeAbove hp B := rfl
end QEC.Coding.TannerLiftedProduct
