-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSResiduePrime.degree_nonzero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:03.411194+00:00
-- url     : https://prove2.me/submissions/a138a723-dbff-4187-9682-4e727ad93b05

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
    (p : ZMod a.q) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact Nat.not_dvd_of_pos_of_lt a.degreePrime.pos
    (by
      have hp : 0 < p := a.degreePrime.pos
      have hlarge := a.large
      omega)
end LPSResiduePrime
end QEC.Coding.TannerLiftedProduct
