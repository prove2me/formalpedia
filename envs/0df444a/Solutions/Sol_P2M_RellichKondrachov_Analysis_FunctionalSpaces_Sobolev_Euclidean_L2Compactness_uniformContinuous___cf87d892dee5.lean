-- Prove2me | solution 1 for P2M_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_uniformContinuous___cf87d892dee5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T22:38:09.634686+00:00
-- url     : https://prove2.me/submissions/855788c8-8b25-4fb8-8bb9-4dda2a2593bf

import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Smoothing
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.UniformSpace.HeineCantor
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Compactness
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply

set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
open scoped ENNReal MeasureTheory Topology Convolution Pointwise
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instBorelSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instOpensMeasurableSpaceEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableAddEL2CompactnessCompactness
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.instMeasurableNegEL2CompactnessCompactness
variable {K : Set E}
variable {ψ : E → ℝ}
omit [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
theorem _root_.solution (hψc : Continuous ψ) (hψcs : HasCompactSupport ψ) :
    UniformContinuous ψ := by
  classical
  -- `HasCompactSupport` implies `ψ = 0` outside a compact set, hence `ψ → 0` along `cocompact`.
  refine
    Continuous.uniformContinuous_of_tendsto_cocompact (f := ψ) (x := (0 : ℝ)) hψc ?_
  -- Show `ψ → 0` along `cocompact` using the `ε`-ball characterization.
  refine (Metric.tendsto_nhds.2 ?_)
  intro ε hε
  refine Filter.mem_cocompact'.mpr ⟨tsupport ψ, hψcs, ?_⟩
  intro x hx
  -- If `ψ x` is `ε`-far from `0`, then `ψ x ≠ 0`, hence `x` belongs to the support and therefore
  -- to the topological support.
  have hx' : ¬ dist (ψ x) 0 < ε := by
    simpa [Set.mem_compl_iff, Set.mem_ofPred_eq] using hx
  have hxε : ε ≤ dist (ψ x) 0 := le_of_not_gt (by simpa [gt_iff_lt] using hx')
  have hx0 : ψ x ≠ 0 := by
    intro hψ0
    have : dist (ψ x) 0 = 0 := by simp [hψ0]
    have : ε ≤ 0 := by simpa [this] using hxε
    exact not_lt_of_ge this hε
  have hx_supp : x ∈ Function.support ψ := by
    simpa [Function.support] using hx0
  have hx_tsupp : x ∈ tsupport ψ := by
    have : x ∈ closure (Function.support ψ) := subset_closure hx_supp
    simpa [tsupport] using this
  exact hx_tsupp
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness
