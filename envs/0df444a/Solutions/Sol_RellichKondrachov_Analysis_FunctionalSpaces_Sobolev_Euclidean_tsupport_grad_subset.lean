-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.tsupport_grad_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:45.672636+00:00
-- url     : https://prove2.me/submissions/cd6a8ad2-2961-4896-8787-0e0170353dfe

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.Topology.Algebra.Support
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory
open MeasureTheory
variable
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceH1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceH1
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceH1
variable (μ : Measure E) [IsFiniteMeasureOnCompacts μ]
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution (f : E → ℝ) : tsupport (grad (E := E) f) ⊆ tsupport f := by
  have hcomp :
      tsupport (grad (E := E) f) ⊆ tsupport (fderiv ℝ f) := by
    exact
      (tsupport_comp_subset
        (g := (InnerProductSpace.toDual ℝ E).symm) (hg := by simp)
        (f := fderiv ℝ f))
  exact hcomp.trans (tsupport_fderiv_subset (𝕜 := ℝ) (f := f))
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
