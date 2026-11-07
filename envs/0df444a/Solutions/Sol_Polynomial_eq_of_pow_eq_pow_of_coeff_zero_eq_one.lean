-- Prove2me | solution 1 for Polynomial.eq_of_pow_eq_pow_of_coeff_zero_eq_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-06T15:05:05.796739+00:00
-- url     : https://prove2.me/submissions/fcc97bd5-6150-4186-97eb-811ef9ca9647

import Mathlib.RingTheory.Norm.Basic
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.LinearAlgebra.Matrix.StdBasis
import Mathlib.RingTheory.TensorProduct.Free
import Mathlib.Tactic.NoncommRing
import Definitions.Def_QEC_Coding_HighDimensionalExpander_Algebra_MatrixAlgebraNorm

set_option autoImplicit false
open scoped Matrix
open Polynomial
namespace Polynomial
theorem _root_.solution
    {R : Type*} [CommRing R]
    {f g : R[X]} {n : ℕ}
    (hn : IsUnit (n : R))
    (hf : f.coeff 0 = 1) (hg : g.coeff 0 = 1)
    (hpow : f ^ n = g ^ n) :
    f = g := by
  let s : R[X] := ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i)
  have hproduct : (f - g) * s = 0 := by
    rw [show (f - g) * s = f ^ n - g ^ n by
      exact (Commute.all f g).mul_geom_sum₂ n]
    rw [hpow, sub_self]
  have hfe : f.eval 0 = 1 := by
    simpa [coeff_zero_eq_eval_zero] using hf
  have hge : g.eval 0 = 1 := by
    simpa [coeff_zero_eq_eval_zero] using hg
  have hscoeff : s.coeff 0 = (n : R) := by
    rw [coeff_zero_eq_eval_zero]
    rw [show s = ∑ i ∈ Finset.range n, f ^ i * g ^ (n - 1 - i) by rfl,
      eval_finsetSum]
    simp [hfe, hge]
  apply sub_eq_zero.mp
  apply eq_zero_of_mul_eq_zero_of_smul s
  · intro a ha
    have hacoeff := congrArg (fun p : R[X] ↦ p.coeff 0) ha
    change (a • s).coeff 0 = (0 : R[X]).coeff 0 at hacoeff
    rw [coeff_smul, hscoeff, coeff_zero] at hacoeff
    exact hn.mul_right_cancel (by simpa [smul_eq_mul] using hacoeff)
  · simpa [mul_comm] using hproduct
end Polynomial
