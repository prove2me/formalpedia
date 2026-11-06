-- Prove2me | solution 1 for RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.isCompactOperator_h1OnToL2_codRestrict_range_extendByZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-05T23:09:01.57441+00:00
-- url     : https://prove2.me/submissions/69ef8031-ce63-4ce3-8e9f-0d6a1cd4468c

import Mathlib.Analysis.Normed.Operator.Compact.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Function.LpSpace.Complete
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_TranslationEstimateH1
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_FrechetKolmogorov
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_Kernels
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_TranslationIntegral
import Definitions.Def_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_Rellich
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_isCompactOperator_h1OnToL2
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_isClosed_range_extendByZero
import Theorems.Thm_RellichKondrachov_Analysis_FunctionalSpaces_Sobolev_Euclidean_L2Compactness_smoothBCF_apply
attribute [local simp] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.L2Compactness.smoothBCF_apply



set_option autoImplicit true
open RellichKondrachov
open RellichKondrachov.Analysis
open RellichKondrachov.Analysis.FunctionalSpaces
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev
open RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
open scoped ENNReal MeasureTheory Topology
open MeasureTheory Set
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instBorelSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instOpensMeasurableSpaceRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableAddRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instMeasurableNegRellich
attribute [local instance] RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean.instFactOneLeTwoSobolevEuclideanRellich
namespace RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
theorem _root_.solution {K : Set E} (hK : IsCompact K)
    (hKm : MeasurableSet K) :
    IsCompactOperator
      (Set.codRestrict
        (h1OnToL2 (E := E) K hKm)
        (LinearMap.range
          ((MeasureTheory.Lp.extendByZeroₗᵢ
                (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
        (by
          intro x
          have hxmem : (x : ↥(h1 (μ := (volume : Measure E)) (E := E))) ∈ h1On (E := E) K hKm :=
            x.property
          dsimp [h1On] at hxmem
          -- Rewrite the codomain-restricted inclusion as `h1ToL2` on the underlying `H¹` element.
          change
              ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                    (x : ↥(h1 (μ := (volume : Measure E)) (E := E)))) ∈
                LinearMap.range
                  ((MeasureTheory.Lp.extendByZeroₗᵢ
                        (μ := (volume : Measure E)) (E := ℝ)
                        (p := (2 : ℝ≥0∞))
                        (s := K) hKm).toLinearMap)
          -- This is exactly the unfolded membership in
          -- the `comap`.
          exact hxmem)) := by
  -- First, use Euclidean Rellich compactness into `L²(volume)`.
  have hcomp : IsCompactOperator (h1OnToL2 (E := E) K hKm) :=
    isCompactOperator_h1OnToL2 (E := E) (K := K) hK hKm
  -- Now codomain-restrict using the closedness of the range.
  -- `hV` is definitional from the codomain restriction in the statement (unification fills it).
  exact
    IsCompactOperator.codRestrict (f := h1OnToL2 (E := E) K hKm) hcomp
      (V := LinearMap.range
        ((MeasureTheory.Lp.extendByZeroₗᵢ
              (μ := (volume : Measure E)) (E := ℝ) (p := (2 : ℝ≥0∞)) (s := K) hKm).toLinearMap))
      (hV := by
        intro x
        have hxmem : (x : ↥(h1 (μ := (volume : Measure E)) (E := E))) ∈ h1On (E := E) K hKm :=
          x.property
        dsimp [h1On] at hxmem
        change
            ((h1ToL2 (μ := (volume : Measure E)) (E := E)).toLinearMap
                  (x : ↥(h1 (μ := (volume : Measure E)) (E := E)))) ∈
              LinearMap.range
                ((MeasureTheory.Lp.extendByZeroₗᵢ
                      (μ := (volume : Measure E)) (E := ℝ)
                      (p := (2 : ℝ≥0∞))
                      (s := K) hKm).toLinearMap)
        exact hxmem)
      (h_closed :=
        isClosed_range_extendByZero (E := E) K hKm)
end RellichKondrachov.Analysis.FunctionalSpaces.Sobolev.Euclidean
