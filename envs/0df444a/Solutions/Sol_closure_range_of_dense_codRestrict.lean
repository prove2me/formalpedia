-- Prove2me | solution 1 for closure_range_of_dense_codRestrict
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T09:35:55.930203+00:00
-- url     : https://prove2.me/submissions/576bc121-9bdc-445e-981f-34b871b16642

import Definitions.Def_auto_M04_6e37b463_SolvesMartingaleProblem
import Definitions.Def_auto_M04_6e37b463_UniformBoundedFunction
import Definitions.Def_auto_M04_6e37b463_processPast
import Mathlib.Algebra.Module.Submodule.LinearMap
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Set.Finite.Lemmas
import Mathlib.LinearAlgebra.Prod
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Measure.FiniteMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Topology.Algebra.Support
import Mathlib.Topology.Continuous
import Mathlib.Topology.ContinuousMap.Weierstrass
import Mathlib.Topology.Instances.NNReal.Lemmas
import Mathlib.Topology.UniformSpace.UniformEmbedding
open MeasureTheory Filter TopologicalSpace
open scoped ENNReal NNReal Topology
open EthierKurtz Classical

theorem closure_range_of_dense_codRestrict
    {D U : Type*} [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (L : Submodule ℝ U) (f : D →ₗ[ℝ] U)
    (hmem : ∀ x, f x ∈ L)
    (hclosed : IsClosed (L : Set U))
    (hdense : DenseRange (LinearMap.codRestrict L f hmem)) :
    closure (Set.range f) = (L : Set U) := by
  have hr : Set.range f = Subtype.val '' Set.range (LinearMap.codRestrict L f hmem) := by
    rw [← Set.range_comp]
    rfl
  rw [hr]
  apply le_antisymm
  · apply closure_minimal _ hclosed
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  · intro y hy
    exact image_closure_subset_closure_image continuous_subtype_val ⟨⟨y, hy⟩, hdense ⟨y, hy⟩, rfl⟩

theorem solution
    {D U : Type*} [AddCommMonoid D] [Module ℝ D]
    [NormedAddCommGroup U] [NormedSpace ℝ U]
    (L : Submodule ℝ U) (f : D →ₗ[ℝ] U)
    (hmem : ∀ x, f x ∈ L)
    (hclosed : IsClosed (L : Set U))
    (hdense : DenseRange (LinearMap.codRestrict L f hmem)) :
    closure (Set.range f) = (L : Set U) := by
  have hr : Set.range f = Subtype.val '' Set.range (LinearMap.codRestrict L f hmem) := by
    rw [← Set.range_comp]
    rfl
  rw [hr]
  apply le_antisymm
  · apply closure_minimal _ hclosed
    rintro _ ⟨x, _, rfl⟩
    exact x.2
  · intro y hy
    exact image_closure_subset_closure_image continuous_subtype_val ⟨⟨y, hy⟩, hdense ⟨y, hy⟩, rfl⟩


