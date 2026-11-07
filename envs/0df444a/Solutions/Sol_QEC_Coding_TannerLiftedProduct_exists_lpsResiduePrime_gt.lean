-- Prove2me | solution 1 for QEC.Coding.TannerLiftedProduct.exists_lpsResiduePrime_gt
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T21:31:06.448211+00:00
-- url     : https://prove2.me/submissions/981e3d5c-d8c1-4e27-a726-aad15772c74f

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
    ∃ a : LPSResiduePrime p, B < a.q := by
  obtain ⟨q, hqBound, hqPrime, hqMod⟩ :=
    Nat.forall_exists_prime_gt_and_modEq (max B (4 * p))
      (q := 4 * p) (a := 1)
      (mul_ne_zero (by norm_num) hp.ne_zero) (by simp)
  letI : Fact q.Prime := ⟨hqPrime⟩
  letI : Fact p.Prime := ⟨hp⟩
  have hqModFour : q % 4 = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hqMod)
    norm_num
  have hqModP : q % p = 1 := by
    apply Nat.mod_eq_of_modEq (Nat.ModEq.of_dvd (by simp) hqMod)
    exact hp.one_lt
  have hqNeTwo : q ≠ 2 := by
    omega
  have hresidue : @legendreSym q ⟨hqPrime⟩ p = 1 := by
    change legendreSym q (p : ℤ) = 1
    rw [legendreSym.quadratic_reciprocity_one_mod_four hp4 hqNeTwo,
      legendreSym.mod]
    have hmod : (q : ℤ) % p = 1 := by
      exact_mod_cast hqModP
    rw [hmod]
    simp
  exact ⟨⟨hp, hp4, q, hqPrime,
      lt_of_le_of_lt (Nat.le_max_right B (4 * p)) hqBound,
      hqModFour, hresidue⟩,
    lt_of_le_of_lt (Nat.le_max_left B (4 * p)) hqBound⟩
end QEC.Coding.TannerLiftedProduct
