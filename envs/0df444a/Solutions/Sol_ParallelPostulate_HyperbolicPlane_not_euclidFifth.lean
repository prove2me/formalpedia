-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.not_euclidFifth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:20:15.177359+00:00
-- url     : https://prove2.me/submissions/96f00c82-dd22-4929-950d-8caef09a267b

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_within
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_sides
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_angles
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_realLeaningFigure_never_meets
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_Between_symm


set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
open Real
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution : ¬ EuclidFifth (-1) := by
  intro h
  obtain ⟨h0, h1, hb, hc⟩ := realLeaningFigure_within
  obtain ⟨sb, sc⟩ := realLeaningFigure_sides
  obtain ⟨t, u, -, -, htu, ht, -⟩ :=
    h realLeaningFigure h0 h1 hb hc sb sc realLeaningFigure_angles
  have hmem : realLeaningFigure.b.pt t ∈ (realLeaningFigure.b.points ∩ plane (-1 : ℝ))
      ∩ (realLeaningFigure.c.points ∩ plane (-1 : ℝ)) :=
    ⟨⟨⟨t, rfl⟩, ht⟩, ⟨⟨u, htu.symm⟩, ht⟩⟩
  rw [realLeaningFigure_never_meets] at hmem
  exact hmem
end ParallelPostulate.HyperbolicPlane
