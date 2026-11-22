-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.angle_congruence_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:15.113887+00:00
-- url     : https://prove2.me/submissions/3c46e9d1-3407-4f32-9604-d0ccdc8f1bd6

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Set Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution {κ : ℝ} {A B C D E F P Q R : ℝ × ℝ}
    (h1 : kleinAngle κ A B C = kleinAngle κ D E F) (h2 : kleinAngle κ A B C = kleinAngle κ P Q R) :
    kleinAngle κ D E F = kleinAngle κ P Q R :=
  h1.symm.trans h2
end ParallelPostulate.HyperbolicPlane
