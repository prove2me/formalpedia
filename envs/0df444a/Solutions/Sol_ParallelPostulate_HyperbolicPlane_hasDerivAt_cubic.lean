-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.hasDerivAt_cubic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:15:32.285379+00:00
-- url     : https://prove2.me/submissions/3c81a814-1f3c-4bdc-bb03-b91dce3df247

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

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Filter Topology
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (c0 c1 c2 c3 : ℝ) {f : ℝ → ℝ}
    (hf : ∀ s, f s = c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3) (t : ℝ) :
    HasDerivAt f (c1 + 2 * c2 * t + 3 * c3 * t ^ 2) t := by
  have e : f = fun s => c0 + c1 * s + c2 * s ^ 2 + c3 * s ^ 3 := funext hf
  subst e
  have h1 : HasDerivAt (fun s : ℝ => c1 * s) (c1 * 1) t :=
    HasDerivAt.const_mul c1 (hasDerivAt_id' t)
  have h2 : HasDerivAt (fun s : ℝ => c2 * s ^ 2) (c2 * (↑2 * t ^ (2 - 1))) t :=
    HasDerivAt.const_mul c2 (hasDerivAt_pow 2 t)
  have h3 : HasDerivAt (fun s : ℝ => c3 * s ^ 3) (c3 * (↑3 * t ^ (3 - 1))) t :=
    HasDerivAt.const_mul c3 (hasDerivAt_pow 3 t)
  have h := HasDerivAt.add (HasDerivAt.add (HasDerivAt.add (hasDerivAt_const t c0) h1) h2) h3
  exact HasDerivAt.congr_deriv h (by norm_num; ring)
end ParallelPostulate.HyperbolicPlane
