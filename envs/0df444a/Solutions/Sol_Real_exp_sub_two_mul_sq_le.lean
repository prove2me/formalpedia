-- Prove2me | solution 1 for Real.exp_sub_two_mul_sq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T03:06:06.281077+00:00
-- url     : https://prove2.me/submissions/46556bd8-6e6a-4455-9687-b5f51696f0d6

module
public import Mathlib.Analysis.Convex.Cone.Extension
public import Mathlib.Analysis.Complex.Exponential
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Analysis.InnerProductSpace.Dual
public import Mathlib.Analysis.InnerProductSpace.Trace
public import Mathlib.Analysis.LocallyConvex.HahnBanach
public import Mathlib.Analysis.Normed.Module.Span
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Definitions.Def_BasicResults_JohnIngredients

set_option autoImplicit true
@[expose] public section
public section
open scoped InnerProductSpace ComplexConjugate
namespace Real
theorem _root_.solution {a : ℝ} (ha : -(1 / 2) ≤ a) :
    Real.exp (a - 2 * a ^ 2) ≤ 1 + a := by
  have h₂ : Real.exp (a - 2 * a ^ 2) = (Real.exp (2 * a ^ 2 - a))⁻¹ := by
    rw [← Real.exp_neg]; ring_nf
  have hexp := Real.add_one_le_exp (2 * a ^ 2 - a)
  rw [h₂, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  nlinarith [mul_nonneg (sq_nonneg a) (by linarith : (0 : ℝ) ≤ 1 + 2 * a),
    mul_nonneg (by linarith : (0 : ℝ) ≤ 1 + a)
      (by linarith : (0 : ℝ) ≤ Real.exp (2 * a ^ 2 - a) - 1 - (2 * a ^ 2 - a))]
end Real
