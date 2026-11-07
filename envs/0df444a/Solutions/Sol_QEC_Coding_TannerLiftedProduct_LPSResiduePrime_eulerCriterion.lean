-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSResiduePrime.eulerCriterion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:04.819174+00:00
-- url     : https://prove2.me/submissions/97db1b54-7841-4afb-b61d-f2c688f24539

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
    (p : ZMod a.q) ^ (a.q / 2) = 1 := by
  have h := legendreSym.eq_pow a.q (p : ℤ)
  simpa [a.residue] using h.symm
end LPSResiduePrime
end QEC.Coding.TannerLiftedProduct
