-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.hasDerivAt_div_cube
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:13:18.481952+00:00
-- url     : https://prove2.me/submissions/3923e55e-e868-486c-8ec2-b5d76553191d

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
    HasDerivAt (fun s => f s / b s ^ 3) ((f' * b t - 3 * f t * b') / b t ^ 4) t := by
  convert! hf.div (hb.pow 3) (pow_ne_zero 3 h) using 1
  try simp only [Pi.pow_apply]
  field_simp
  ring
end ParallelPostulate.HyperbolicPlane
