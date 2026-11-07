-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSResiduePrime.ne_degreePrime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:15.979445+00:00
-- url     : https://prove2.me/submissions/2c800967-a6b2-4eff-8f07-b16d8b5d2b19

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
namespace LPSResiduePrime
theorem _root_.solution (a : LPSResiduePrime p) :
    a.q ≠ p := by
  have hp : 0 < p := a.degreePrime.pos
  have hlarge := a.large
  omega
end LPSResiduePrime
end QEC.Coding.TannerLiftedProduct
