-- Prove2me | solution 2 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.grad_translate
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:37:46.552352+00:00
-- url     : https://prove2.me/submissions/2c45c838-3a60-4568-8ffb-2c056fcefc98

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution (a : E) (f : E → ℝ) (x : E) :
    grad (E := E) (translate (E := E) a f) x = grad (E := E) f (x + a) := by
  classical
  -- `fderiv` commutes with translation, hence so does `grad`.
  -- Reduce to the standard `fderiv` translation lemma, applied under the Riesz dual map.
  have hfderiv : fderiv ℝ (translate (E := E) a f) x = fderiv ℝ f (x + a) :=
    fderiv_comp_add_right (𝕜 := ℝ) (f := f) (x := x) a
  simp only [grad, hfderiv]
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
