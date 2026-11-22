-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.kleinInner_aux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:15:16.391439+00:00
-- url     : https://prove2.me/submissions/c38ee771-e4b1-4902-b26d-8449f3a16b0a

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
theorem _root_.solution (κ a w xP yP xA yA xB yB XP YP XA YA XB YB : K)
    (hw : w ^ 2 = 1 + κ * a ^ 2)
    (hXP : XP * (1 - κ * a * xP) = xP + a) (hYP : YP * (1 - κ * a * xP) = w * yP)
    (hXA : XA * (1 - κ * a * xA) = xA + a) (hYA : YA * (1 - κ * a * xA) = w * yA)
    (hXB : XB * (1 - κ * a * xB) = xB + a) (hYB : YB * (1 - κ * a * xB) = w * yB) :
    ((XA - XP) * (XB - XP) + (YA - YP) * (YB - YP)
        + κ * (XP * YA - YP * XA) * (XP * YB - YP * XB))
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xA) * (1 - κ * a * xB))
      = w ^ 4 * ((xA - xP) * (xB - xP) + (yA - yP) * (yB - yP)
        + κ * (xP * yA - yP * xA) * (xP * yB - yP * xB)) := by
  have e1 : (XA - XP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
      = (xA + a) * (1 - κ * a * xP) - (xP + a) * (1 - κ * a * xA) := by
    linear_combination (1 - κ * a * xP) * hXA - (1 - κ * a * xA) * hXP
  have e2 : (XB - XP) * ((1 - κ * a * xB) * (1 - κ * a * xP))
      = (xB + a) * (1 - κ * a * xP) - (xP + a) * (1 - κ * a * xB) := by
    linear_combination (1 - κ * a * xP) * hXB - (1 - κ * a * xB) * hXP
  have e3 : (YA - YP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
      = w * (yA * (1 - κ * a * xP) - yP * (1 - κ * a * xA)) := by
    linear_combination (1 - κ * a * xP) * hYA - (1 - κ * a * xA) * hYP
  have e4 : (YB - YP) * ((1 - κ * a * xB) * (1 - κ * a * xP))
      = w * (yB * (1 - κ * a * xP) - yP * (1 - κ * a * xB)) := by
    linear_combination (1 - κ * a * xP) * hYB - (1 - κ * a * xB) * hYP
  have e5 : (XP * YA - YP * XA) * ((1 - κ * a * xP) * (1 - κ * a * xA))
      = w * ((xP + a) * yA - yP * (xA + a)) := by
    linear_combination (YA * (1 - κ * a * xA)) * hXP + (xP + a) * hYA
      - (XA * (1 - κ * a * xA)) * hYP - (w * yP) * hXA
  have e6 : (XP * YB - YP * XB) * ((1 - κ * a * xP) * (1 - κ * a * xB))
      = w * ((xP + a) * yB - yP * (xB + a)) := by
    linear_combination (YB * (1 - κ * a * xB)) * hXP + (xP + a) * hYB
      - (XB * (1 - κ * a * xB)) * hYP - (w * yP) * hXB
  have e : ((XA - XP) * (XB - XP) + (YA - YP) * (YB - YP)
        + κ * (XP * YA - YP * XA) * (XP * YB - YP * XB))
        * ((1 - κ * a * xP) ^ 2 * (1 - κ * a * xA) * (1 - κ * a * xB))
      = (XA - XP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
          * ((XB - XP) * ((1 - κ * a * xB) * (1 - κ * a * xP)))
        + (YA - YP) * ((1 - κ * a * xA) * (1 - κ * a * xP))
          * ((YB - YP) * ((1 - κ * a * xB) * (1 - κ * a * xP)))
        + κ * ((XP * YA - YP * XA) * ((1 - κ * a * xP) * (1 - κ * a * xA)))
          * ((XP * YB - YP * XB) * ((1 - κ * a * xP) * (1 - κ * a * xB))) := by ring
  rw [e, e1, e2, e3, e4, e5, e6]
  linear_combination
    ((yA * (1 - κ * a * xP) - yP * (1 - κ * a * xA))
        * (yB * (1 - κ * a * xP) - yP * (1 - κ * a * xB))
      + κ * ((xP + a) * yA - yP * (xA + a)) * ((xP + a) * yB - yP * (xB + a))
      - (w ^ 2 + 1 + κ * a ^ 2) * ((xA - xP) * (xB - xP) + (yA - yP) * (yB - yP)
        + κ * (xP * yA - yP * xA) * (xP * yB - yP * xB))) * hw
end ParallelPostulate.HyperbolicPlane
