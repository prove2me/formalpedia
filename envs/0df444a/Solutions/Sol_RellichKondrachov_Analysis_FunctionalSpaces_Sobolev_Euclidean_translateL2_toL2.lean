-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.translateL2_toL2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:08:50.258011+00:00
-- url     : https://prove2.me/submissions/c105a5fb-f1f3-4bb5-94dd-b6904f1512d9

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_H1
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Topology.Algebra.Group.Basic
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Translation
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_translateL2_ae_eq

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceTranslation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceTranslation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceTranslation
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddTranslation
variable (μ : Measure E) [μ.IsAddRightInvariant]
variable [IsFiniteMeasureOnCompacts μ]
omit [CompleteSpace E]
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution (a : E) (f : ↥(C1c (E := E))) :
    translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) =
      toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) := by
  apply Lp.ext
  have h₁ :
      (translateL2 (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    have hf : (toL2 (μ := μ) (E := E) f : E → ℝ) =ᵐ[μ] f.1 :=
      (memLp_of_mem_C1c (μ := μ) (E := E) f.2).coeFn_toLp
    have hf' :
        (fun x => (toL2 (μ := μ) (E := E) f : E → ℝ) (x + a)) =ᵐ[μ] fun x => f.1 (x + a) := by
      -- Move the a.e. equality through a measure-preserving map.
      exact
        (Measure.QuasiMeasurePreserving.ae_eq_comp
          (MeasureTheory.measurePreserving_add_right μ a).quasiMeasurePreserving hf)
    exact (translateL2_ae_eq (μ := μ) (F := ℝ) a (toL2 (μ := μ) (E := E) f)).trans hf'
  have h₂ :
      (toL2 (μ := μ) (E := E) (translateC1c (E := E) a f) : E → ℝ) =ᵐ[μ]
        fun x => f.1 (x + a) := by
    -- `toL2` agrees a.e. with the underlying translated function.
    exact
      (memLp_of_mem_C1c (μ := μ) (E := E) (translateC1c (E := E) a f).2).coeFn_toLp
  exact h₁.trans h₂.symm
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
