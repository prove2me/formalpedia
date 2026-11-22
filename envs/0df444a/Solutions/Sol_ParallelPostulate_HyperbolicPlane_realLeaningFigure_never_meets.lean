-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.realLeaningFigure_never_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:16:08.681529+00:00
-- url     : https://prove2.me/submissions/a7796d23-da2d-4a66-a501-341da3504da3

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
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution :
    (realLeaningFigure.b.points ∩ plane (-1 : ℝ)) ∩ (realLeaningFigure.c.points ∩ plane (-1 : ℝ))
      = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro X ⟨⟨⟨t, rfl⟩, hX⟩, ⟨⟨u, hu⟩, -⟩⟩
  have e1 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  simp only [realLeaningFigure, Dim.pt] at e1 e2
  have hu10 : u = 10 := by linarith
  have ht10 : t = 10 := by linarith
  rw [ht10] at hX
  norm_num [realLeaningFigure, Dim.pt, plane] at hX
end ParallelPostulate.HyperbolicPlane
