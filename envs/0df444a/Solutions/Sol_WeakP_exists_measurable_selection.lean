-- Prove2me | solution 1 for WeakP.exists_measurable_selection
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:30:42.188018+00:00
-- url     : https://prove2.me/submissions/9dd983a7-82de-4a95-8131-2e823b4b3752

import Definitions.Def_BicausalOT_MeasurableStrategy
import Definitions.Def_BicausalOT_DescriptiveSetTheory_CouplingsUHC
import Definitions.Def_BicausalOT_DescriptiveSetTheory_LscIntegral
import Definitions.Def_BicausalOT_DescriptiveSetTheory_MeasurableSelection
import Definitions.Def_BicausalOT_LscBellman
import Theorems.Thm_exists_measurable_selection

section
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
private theorem WeakP.krm_selection_delegate {α : Type*} [MeasurableSpace α]
    {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [PolishSpace W]
    [BorelSpace W]
    {Φ : α → Set (WeakP W)} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set (WeakP W), IsOpen U →
      MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → WeakP W, Measurable f ∧ ∀ a, f a ∈ Φ a := by
  letI := TopologicalSpace.upgradeIsCompletelyMetrizable (WeakP W)
  exact _root_.exists_measurable_selection hne hclosed hmeas
namespace MultiPeriod
variable {X Y : ℕ → Type*}
  [∀ n, TopologicalSpace (X n)] [∀ n, PolishSpace (X n)]
  [∀ n, MeasurableSpace (X n)] [∀ n, BorelSpace (X n)]
  [∀ n, TopologicalSpace (Y n)] [∀ n, PolishSpace (Y n)]
  [∀ n, MeasurableSpace (Y n)] [∀ n, BorelSpace (Y n)]
variable (κμP : (t : ℕ) → XHist X t → ProbabilityMeasure (X (t + 1)))
variable (κνP : (t : ℕ) → YHist Y t → ProbabilityMeasure (Y (t + 1)))
variable (c : (t : ℕ) → PairHist X Y t → ℝ≥0∞)
end MultiPeriod
end
end

set_option autoImplicit false
open MeasureTheory Set Filter Topology
open scoped ENNReal
noncomputable section
namespace WeakP
theorem _root_.solution {α : Type*} [MeasurableSpace α]
    {W : Type*} [MeasurableSpace W] [TopologicalSpace W] [PolishSpace W]
    [BorelSpace W]
    {Φ : α → Set (WeakP W)} (hne : ∀ a, (Φ a).Nonempty)
    (hclosed : ∀ a, IsClosed (Φ a))
    (hmeas : ∀ U : Set (WeakP W), IsOpen U →
      MeasurableSet {a | (Φ a ∩ U).Nonempty}) :
    ∃ f : α → WeakP W, Measurable f ∧ ∀ a, f a ∈ Φ a :=
  WeakP.krm_selection_delegate hne hclosed hmeas
end WeakP
