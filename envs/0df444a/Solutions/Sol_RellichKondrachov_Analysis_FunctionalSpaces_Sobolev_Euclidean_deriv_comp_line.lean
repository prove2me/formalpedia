-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.deriv_comp_line
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:01:47.549904+00:00
-- url     : https://prove2.me/submissions/a16d9508-815a-4551-a6bb-97ce1edd4378

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimate
set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslationEstimate
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslationEstimate

theorem solution {f : E → ℝ} (hf : ContDiff ℝ 1 f) (x a : E) (t : ℝ) :
    deriv (fun t => f (line (x := x) (a := a) t)) t =
      fderiv ℝ f (line (x := x) (a := a) t) a := by
  have hline : HasDerivAt (fun s : ℝ => line (x := x) (a := a) s) a t := by
    simpa [line] using ((hasDerivAt_id t).smul_const a).const_add x
  have hcomp : HasDerivAt (fun s : ℝ => f (line (x := x) (a := a) s))
      (fderiv ℝ f (line (x := x) (a := a) t) a) t := by
    exact (hf.differentiable one_ne_zero).differentiableAt.hasFDerivAt.comp_hasDerivAt t hline
  exact hcomp.deriv
