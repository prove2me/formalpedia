-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSResiduePrime.sourceResidueCongruence
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:32:10.275723+00:00
-- url     : https://prove2.me/submissions/73802713-804a-4d77-b3c4-7ce6c6f65188

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_eulerCriterion

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
namespace QEC.Coding.TannerLiftedProduct
namespace LPSResiduePrime
theorem _root_.solution (a : LPSResiduePrime p) :
    p ^ ((a.q - 1) / 2) % a.q = 1 := by
  have hhalf : (a.q - 1) / 2 = a.q / 2 := by
    have hmod := a.modFour
    omega
  have hcast :
      ((p ^ ((a.q - 1) / 2) : ℕ) : ZMod a.q) = 1 := by
    simpa [hhalf] using a.eulerCriterion
  have hcast' :
      ((p ^ ((a.q - 1) / 2) : ℕ) : ZMod a.q) =
        ((1 : ℕ) : ZMod a.q) := by
    simpa using hcast
  have hmod := (ZMod.natCast_eq_natCast_iff'
    (p ^ ((a.q - 1) / 2)) 1 a.q).mp hcast'
  exact hmod.trans (Nat.mod_eq_of_lt a.prime.one_lt)
end LPSResiduePrime
end QEC.Coding.TannerLiftedProduct
