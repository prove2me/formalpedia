-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ArtinSchreier.asNoRoot
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T21:42:51.81702+00:00
-- url     : https://prove2.me/submissions/d087abac-6ee4-4783-b4fc-638a379a261a

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier
section
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
private theorem exp_lt_exp {a b : ℤ} : WithZero.exp a < WithZero.exp b ↔ a < b := by
  simp [WithZero.exp]
end QEC.Coding.AlgebraicGeometry.ArtinSchreier
end

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
theorem _root_.solution (ν : Valuation F ℤᵐ⁰) (u : F) (hu : ν u = WithZero.exp (33 : ℤ))
    (y : F) : y ^ 32 + y ≠ u := by
  intro h
  have hν : ν (y ^ 32 + y) = WithZero.exp (33 : ℤ) := by
    rw [h, hu]
  by_cases hy0 : ν y = 0
  · -- y = 0, so u = 0, contradicting `ν u = exp 33 ≠ 0`
    have hy : y = 0 := (Valuation.zero_iff ν).mp hy0
    subst y
    have hu0 : u = 0 := by simpa using h.symm
    rw [hu0, Valuation.map_zero] at hu
    exact WithZero.exp_ne_zero hu.symm
  · -- ν y = exp r for a unique r : ℤ
    let r : ℤ := WithZero.log (ν y)
    have hye : ν y = WithZero.exp r := by
      dsimp [r]
      exact (WithZero.exp_log hy0).symm
    have hνy32 : ν (y ^ 32) = WithZero.exp ((32 : ℕ) • r) := by
      rw [map_pow, hye, ← WithZero.exp_nsmul]
    by_cases hrpos : 0 < r
    · -- y is a pole: `y³²` strictly dominates, `ν (y³² + y) = exp (32·r)`
      have hlt : ν y < ν (y ^ 32) := by
        rw [hye, hνy32]
        exact exp_lt_exp.mpr (by
          rw [nsmul_eq_mul]
          omega)
      have hsum : ν (y ^ 32 + y) = WithZero.exp ((32 : ℕ) • r) := by
        rw [Valuation.map_add_eq_of_lt_left ν hlt, hνy32]
      rw [hsum] at hν
      have h32r : (32 : ℕ) • r = 33 := WithZero.exp_inj.mp hν
      rw [nsmul_eq_mul] at h32r
      omega -- 32·r = 33 has no integer solution
    · by_cases hrneg : r < 0
      · -- y is a zero: `ν (y³²) < ν y`, so `ν (y³² + y) = exp r`
        have hlt : ν (y ^ 32) < ν y := by
          rw [hνy32, hye]
          exact exp_lt_exp.mpr (by
            rw [nsmul_eq_mul]
            omega)
        have hsum : ν (y ^ 32 + y) = ν y := by
          rw [Valuation.map_add_eq_of_lt_right ν hlt]
        rw [hsum, hye] at hν
        have hr33 : r = 33 := WithZero.exp_inj.mp hν
        omega -- r = 33 contradicts r < 0
      · -- r = 0: both summands have valuation 1, so the sum has valuation ≤ 1 < exp 33
        have hr0 : r = 0 := by omega
        have hy1 : ν y = 1 := by simp [hye, hr0]
        have hy321 : ν (y ^ 32) = 1 := by rw [map_pow, hy1, one_pow]
        have hle : ν (y ^ 32 + y) ≤ 1 := by
          have := map_add_le_max ν (y ^ 32) y
          rwa [hy321, hy1] at this
        have hlt1 : 1 < WithZero.exp (33 : ℤ) := exp_lt_exp.mpr (by norm_num)
        rw [hν] at hle
        exact (not_lt_of_ge hle) hlt1
end QEC.Coding.AlgebraicGeometry.ArtinSchreier
