-- Prove2me | solution 1 for QEC.Coding.AlgebraicGeometry.ArtinSchreier.val_of_frobenius_fixed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T19:07:36.838113+00:00
-- url     : https://prove2.me/submissions/1dae20b2-12ca-4d13-9595-23b1bcb307c7

import Mathlib
import Definitions.Def_QEC_Coding_AlgebraicGeometry_Towers_ArtinSchreier

set_option autoImplicit false
open QEC QEC.Coding QEC.Coding.AlgebraicGeometry QEC.Coding.AlgebraicGeometry.ArtinSchreier
open scoped WithZero BigOperators
open Polynomial
variable {F : Type*} [Field F]
namespace QEC.Coding.AlgebraicGeometry.ArtinSchreier
theorem _root_.solution (ν : Valuation F ℤᵐ⁰) {c : F} (hc : c ^ 32 = c) :
    ν c = 0 ∨ ν c = 1 := by
  have hν : (ν c) ^ 32 = ν c := by
    simpa [map_pow] using congrArg ν hc
  by_cases h0 : ν c = 0
  · exact Or.inl h0
  · right
    have hce : ν c = WithZero.exp (WithZero.log (ν c)) := (WithZero.exp_log h0).symm
    rw [hce] at hν
    rw [← WithZero.exp_nsmul] at hν
    have hlog32 : (32 : ℕ) • WithZero.log (ν c) = WithZero.log (ν c) :=
      WithZero.exp_inj.mp hν
    have hlog0 : WithZero.log (ν c) = 0 := by
      rw [nsmul_eq_mul] at hlog32
      omega
    rw [hce, hlog0]
    simp
end QEC.Coding.AlgebraicGeometry.ArtinSchreier
