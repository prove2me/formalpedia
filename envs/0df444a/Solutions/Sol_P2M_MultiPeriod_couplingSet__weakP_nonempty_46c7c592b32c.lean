-- Prove2me | solution 1 for P2M_MultiPeriod_couplingSet__weakP_nonempty_46c7c592b32c
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:32:49.780334+00:00
-- url     : https://prove2.me/submissions/5cf3e095-90fb-4a2f-a572-c60bbe86eedd

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_MeasureTheory_Measure_map_fst_prod_of_isProbabilityMeasure
import Theorems.Thm_MeasureTheory_Measure_map_snd_prod_of_isProbabilityMeasure


set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
open MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
omit [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, BorelSpace (X n)] [∀ n, TopologicalSpace (Y n)]
  [∀ n, BorelSpace (Y n)]
namespace MultiPeriod
theorem _root_.solution
    (μ₀ : Measure (X 0)) [IsProbabilityMeasure μ₀]
    (ν₀ : Measure (Y 0)) [IsProbabilityMeasure ν₀] :
    {γ : WeakP (X 0 × Y 0) | γ.toMeasure ∈ CouplingSet₀ μ₀ ν₀}.Nonempty :=
  ⟨show WeakP (X 0 × Y 0) from
      (⟨μ₀.prod ν₀, inferInstance⟩ : ProbabilityMeasure (X 0 × Y 0)),
    Measure.map_fst_prod_of_isProbabilityMeasure μ₀ ν₀,
    Measure.map_snd_prod_of_isProbabilityMeasure μ₀ ν₀⟩
end MultiPeriod
