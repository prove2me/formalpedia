-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:46.566231+00:00
-- url     : https://prove2.me/submissions/53afee65-c14c-4e6c-9ff3-ffa7bf309163

module
public import Definitions.Def_LeanPool_ParallelPostulate_Geometry
public import Definitions.Def_LeanPool_ParallelPostulate_Hilbert
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.LineDeriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Arsinh
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Definitions.Def_LeanPool_ParallelPostulate
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_cross_aux

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ a w : K) {A B C : K × K} (hA : 1 - κ * a * A.1 ≠ 0)
    (hB : 1 - κ * a * B.1 ≠ 0) (hC : 1 - κ * a * C.1 ≠ 0) :
    cross ((shift κ a w B).1 - (shift κ a w A).1, (shift κ a w B).2 - (shift κ a w A).2)
        ((shift κ a w C).1 - (shift κ a w A).1, (shift κ a w C).2 - (shift κ a w A).2)
      = w * (1 + κ * a ^ 2) * cross (B.1 - A.1, B.2 - A.2) (C.1 - A.1, C.2 - A.2)
          / ((1 - κ * a * A.1) * (1 - κ * a * B.1) * (1 - κ * a * C.1)) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero hA hB) hC)]
  have h := cross_aux κ a w A.1 A.2 B.1 B.2 C.1 C.2 _ _ _ _ _ _
    (div_mul_cancel₀ (A.1 + a) hA) (div_mul_cancel₀ (w * A.2) hA)
    (div_mul_cancel₀ (B.1 + a) hB) (div_mul_cancel₀ (w * B.2) hB)
    (div_mul_cancel₀ (C.1 + a) hC) (div_mul_cancel₀ (w * C.2) hC)
  simp only [shift, cross]
  linear_combination h
end ParallelPostulate.HyperbolicPlane
