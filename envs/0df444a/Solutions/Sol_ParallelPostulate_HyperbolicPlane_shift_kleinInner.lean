-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.shift_kleinInner
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:14.711929+00:00
-- url     : https://prove2.me/submissions/3d4bcf8e-f631-418e-ba7c-a8253a3e9eb3

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_kleinInner_aux

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ a w : K} (hw : w ^ 2 = 1 + κ * a ^ 2) {P A B : K × K}
    (hP : 1 - κ * a * P.1 ≠ 0) (hA : 1 - κ * a * A.1 ≠ 0) (hB : 1 - κ * a * B.1 ≠ 0) :
    kleinInner κ (shift κ a w P) (shift κ a w A) (shift κ a w B)
      = w ^ 4 * kleinInner κ P A B
          / ((1 - κ * a * P.1) ^ 2 * (1 - κ * a * A.1) * (1 - κ * a * B.1)) := by
  rw [eq_div_iff (mul_ne_zero (mul_ne_zero (pow_ne_zero 2 hP) hA) hB)]
  have h := kleinInner_aux κ a w P.1 P.2 A.1 A.2 B.1 B.2 _ _ _ _ _ _ hw
    (div_mul_cancel₀ (P.1 + a) hP) (div_mul_cancel₀ (w * P.2) hP)
    (div_mul_cancel₀ (A.1 + a) hA) (div_mul_cancel₀ (w * A.2) hA)
    (div_mul_cancel₀ (B.1 + a) hB) (div_mul_cancel₀ (w * B.2) hB)
  simp only [kleinInner, shift, cross]
  linear_combination h
end ParallelPostulate.HyperbolicPlane
