-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.hasDerivAt_div_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:13:15.415673+00:00
-- url     : https://prove2.me/submissions/a51c0f83-2590-44e7-919b-d386d112451b

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
theorem _root_.solution {f b : ℝ → ℝ} {f' b' t : ℝ} (hf : HasDerivAt f f' t)
    (hb : HasDerivAt b b' t) (h : b t ≠ 0) :
    HasDerivAt (fun s => f s / b s ^ 2) ((f' * b t - 2 * f t * b') / b t ^ 3) t := by
  convert! hf.div (hb.pow 2) (pow_ne_zero 2 h) using 1
  try simp only [Pi.pow_apply]
  field_simp
  ring
end ParallelPostulate.HyperbolicPlane
