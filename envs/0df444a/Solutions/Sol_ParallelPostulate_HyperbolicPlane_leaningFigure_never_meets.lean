-- Prove2me | solution 1 for ParallelPostulate.HyperbolicPlane.leaningFigure_never_meets
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T18:19:25.562481+00:00
-- url     : https://prove2.me/submissions/01059a0a-813a-4ef7-9a7f-26ceda9eae22

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
public import Theorems.Thm_ParallelPostulate_HyperbolicPlane_leaningFigure_meets_beyond

set_option autoImplicit true
@[expose] public section
public section
open ParallelPostulate
open ParallelPostulate.HyperbolicPlane
open Pairs
namespace ParallelPostulate.HyperbolicPlane
theorem _root_.solution :
    (leaningFigure.b.points ∩ plane (-1 : ℚ)) ∩ (leaningFigure.c.points ∩ plane (-1 : ℚ))
      = ∅ := by
  apply Set.eq_empty_of_forall_notMem
  rintro X ⟨⟨⟨t, rfl⟩, hX⟩, ⟨⟨u, hu⟩, -⟩⟩
  have e1 := congrArg Prod.fst hu
  have e2 := congrArg Prod.snd hu
  simp only [leaningFigure, Dim.pt] at e1 e2
  have hu10 : u = 10 := by linarith
  have ht10 : t = 10 := by linarith
  rw [ht10] at hX
  rw [leaningFigure_meets_beyond.1] at hX
  exact leaningFigure_meets_beyond.2.2 hX
end ParallelPostulate.HyperbolicPlane
