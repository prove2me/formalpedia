-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.leaningFigure_hypotheses
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:17.252174+00:00
-- url     : https://prove2.me/submissions/befade9f-346e-4132-8eda-af0524fc6eaf

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_leaningFigure_values

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution :
    0 < leaningFigure.a.side leaningFigure.b.one ∧
      0 < leaningFigure.a.side leaningFigure.c.one ∧
      0 < cross leaningFigure.b.dir leaningFigure.c.dir := by
  obtain ⟨h1, h2, h3⟩ := leaningFigure_values
  rw [h1, h2, h3]
  norm_num
end ParallelPostulate.HyperbolicPlane
