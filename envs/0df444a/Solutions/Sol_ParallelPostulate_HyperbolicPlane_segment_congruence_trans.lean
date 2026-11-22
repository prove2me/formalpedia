-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.segment_congruence_trans
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:04.114341+00:00
-- url     : https://prove2.me/submissions/a445a0cc-f726-4ae5-af9b-26d979adea4b

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
theorem _root_.solution {κ : ℝ} {A B C D E F : ℝ × ℝ}
    (h1 : kleinDist κ A B = kleinDist κ C D) (h2 : kleinDist κ A B = kleinDist κ E F) :
    kleinDist κ C D = kleinDist κ E F :=
  h1.symm.trans h2
end ParallelPostulate.HyperbolicPlane
