-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.LPSResiduePrime.coprime_thetaLevel
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:32:01.966781+00:00
-- url     : https://prove2.me/submissions/a5a6587c-f549-4090-9b9b-2e9ba79cc6ee

import Definitions.Def_QEC_Coding_BalancedProduct_LPSArithmetic
import Mathlib.Data.Nat.Find
import Mathlib.GroupTheory.Coset.Card
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Definitions.Def_QEC_Coding_ExpanderCodes_LPSResiduePrime
import Theorems.Thm_QEC_Coding_TannerLiftedProduct_LPSResiduePrime_ne_degreePrime

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.TannerLiftedProduct
variable {p : ℕ}
open scoped MatrixGroups
open Matrix
namespace QEC.Coding.TannerLiftedProduct
namespace LPSResiduePrime
theorem _root_.solution
    (a : LPSResiduePrime p) : Nat.Coprime p (16 * a.q ^ 2) := by
  have hpTwo : p ≠ 2 := by
    intro h
    have hMod := a.degreeModFour
    norm_num [h] at hMod
  have hp16 : Nat.Coprime p 16 := by
    simpa [show (16 : ℕ) = 2 ^ 4 by norm_num] using
      (((Nat.coprime_primes a.degreePrime Nat.prime_two).2 hpTwo).pow_right 4)
  have hpq : Nat.Coprime p a.q :=
    (Nat.coprime_primes a.degreePrime a.prime).2 a.ne_degreePrime.symm
  exact Nat.Coprime.mul_right hp16 (hpq.pow_right 2)
end LPSResiduePrime
end QEC.Coding.TannerLiftedProduct
