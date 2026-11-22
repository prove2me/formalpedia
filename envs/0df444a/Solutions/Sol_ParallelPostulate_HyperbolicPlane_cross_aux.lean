-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.cross_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:14:51.140522+00:00
-- url     : https://prove2.me/submissions/23d3d4be-750a-46c3-8039-364c3b9416cb

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
variable {K : Type*} [Field K]
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution (κ a w xA yA xB yB xC yC XA YA XB YB XC YC : K)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB)
    (hXC : XC * (1 - κ * a * xC) = xC + a) (hYC : YC * (1 - κ * a * xC) = w * yC) :
    ((XB - XA) * (YC - YA) - (YB - YA) * (XC - XA))
        * ((1 - κ * a * xA) * (1 - κ * a * xB) * (1 - κ * a * xC))
      = w * (1 + κ * a ^ 2) * ((xB - xA) * (yC - yA) - (yB - yA) * (xC - xA)) := by
  linear_combination
    ((1 - κ * a * xA) * (YC * (1 - κ * a * xC))
      - (1 - κ * a * xC) * (YA * (1 - κ * a * xA))) * hXB
    + (-(1 - κ * a * xB) * (YC * (1 - κ * a * xC))
      + (1 - κ * a * xC) * (YB * (1 - κ * a * xB))) * hXA
    + (-(1 - κ * a * xA) * (YB * (1 - κ * a * xB))
      + (1 - κ * a * xB) * (YA * (1 - κ * a * xA))) * hXC
    + ((1 - κ * a * xA) * (xB + a) - (1 - κ * a * xB) * (xA + a)) * hYC
    + (-(1 - κ * a * xC) * (xB + a) + (1 - κ * a * xB) * (xC + a)) * hYA
    + (-(1 - κ * a * xA) * (xC + a) + (1 - κ * a * xC) * (xA + a)) * hYB
end ParallelPostulate.HyperbolicPlane
