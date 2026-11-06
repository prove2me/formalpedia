-- Prove2me | solution 2 for QEC.Coding.AlgebraicGeometry.ArtinSchreier.val_of_frobenius_fixed
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T19:30:23.747008+00:00
-- url     : https://prove2.me/submissions/0a492f46-6f03-4edf-99d3-ce65d99bf65e

import Mathlib
set_option autoImplicit false
open scoped WithZero
variable {F : Type*} [Field F]

theorem solution (ν : Valuation F ℤᵐ⁰) {c : F} (hc : c ^ 32 = c) :
    ν c = 0 ∨ ν c = 1 := by
  by_cases hc0 : c = 0
  · left
    simp [hc0]
  · right
    have hν0 : ν c ≠ 0 := ν.ne_zero_iff.mpr hc0
    have hν : (ν c) ^ 32 = ν c := by
      rw [← map_pow, hc]
    have hlog := congrArg WithZero.log hν
    rw [WithZero.log_pow] at hlog
    have hlog0 : WithZero.log (ν c) = 0 := by
      simp only [nsmul_eq_mul, Nat.cast_ofNat] at hlog
      omega
    rw [← WithZero.exp_log hν0, hlog0, WithZero.exp_zero]
