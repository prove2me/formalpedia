-- Prove2me | solution 1 for ProbabilityMeasureSpace.borelSpace
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-10-31T10:47:00.042111+00:00
-- url     : https://prove2.me/submissions/96ba76de-dd45-42da-9413-400f5ee7fe73

import Mathlib
import Theorems.Thm_ProbabilityMeasureSpace_secondCountableTopology

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BoundedContinuousFunction

theorem solution {X : Type*} [TopologicalSpace X]
    [TopologicalSpace.PseudoMetrizableSpace X] [TopologicalSpace.SeparableSpace X]
    [MeasurableSpace X] [BorelSpace X] :
    BorelSpace (ProbabilityMeasure X) := by
  letI : PseudoMetricSpace X := TopologicalSpace.pseudoMetrizableSpacePseudoMetric X
  haveI : SecondCountableTopology (ProbabilityMeasure X) :=
    ProbabilityMeasureSpace.secondCountableTopology
  -- the evaluation maps
  let g : (X →ᵇ ℝ≥0) → ProbabilityMeasure X → ℝ≥0 := fun f μ => μ.toFiniteMeasure.testAgainstNN f
  have hg : ∀ f, Measurable (g f) := by
    intro f
    have : Measurable fun μ : Measure X => ∫⁻ x, (f x : ℝ≥0∞) ∂μ :=
      Measure.measurable_lintegral (by fun_prop)
    exact (this.comp measurable_subtype_coe).ennreal_toNNReal
  have ht : (inferInstance : TopologicalSpace (ProbabilityMeasure X)) =
      ⨅ f, TopologicalSpace.induced (g f) inferInstance := by
    show TopologicalSpace.induced _ (TopologicalSpace.induced _
      (TopologicalSpace.induced _ Pi.topologicalSpace)) = _
    erw [induced_compose, Pi.topologicalSpace, induced_iInf]
    rw [induced_iInf]
    congr 1
    funext f
    erw [induced_compose, induced_compose]
    rfl
  constructor
  apply le_antisymm
  · -- Giry ≤ Borel
    have key : @Measurable _ _ (borel (ProbabilityMeasure X)) _
        (fun μ : ProbabilityMeasure X => (μ : Measure X)) := by
      letI mb : MeasurableSpace (ProbabilityMeasure X) := borel _
      haveI : BorelSpace (ProbabilityMeasure X) := ⟨rfl⟩
      refine Measurable.measure_of_isPiSystem_of_isProbabilityMeasure
        (S := {s : Set X | IsOpen s}) (BorelSpace.measurable_eq.trans rfl) isPiSystem_isOpen ?_
      intro U hU
      apply LowerSemicontinuous.measurable
      rw [lowerSemicontinuous_iff_le_liminf]
      intro μ
      exact ProbabilityMeasure.le_liminf_measure_open_of_tendsto tendsto_id hU
    exact key.comap_le
  · -- Borel ≤ Giry
    have ht' : (inferInstance : TopologicalSpace (ProbabilityMeasure X)) =
        TopologicalSpace.generateFrom
          (⋃ f, {u | IsOpen[TopologicalSpace.induced (g f) inferInstance] u}) := by
      rw [ht]; exact (generateFrom_iUnion_isOpen _).symm
    rw [borel_eq_generateFrom_of_subbasis ht']
    apply MeasurableSpace.generateFrom_le
    intro u hu
    simp only [Set.mem_iUnion, Set.mem_ofPred_eq] at hu
    obtain ⟨f, hf⟩ := hu
    rw [isOpen_induced_iff] at hf
    obtain ⟨V, hV, rfl⟩ := hf
    exact hg f hV.measurableSet
