-- Prove2me | solution 1 for ProbabilityTheory.identDistrib_map
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:29.226415+00:00
-- url     : https://prove2.me/submissions/92d77b10-b85c-4be6-937d-e6126edf833e

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib

set_option autoImplicit true
@[expose] public section
public section
noncomputable section
open MeasureTheory Measure Filter Set
open scoped Topology MeasureTheory ENNReal NNReal
attribute [symm] ProbabilityTheory.IdentDistrib.symm
variable {α β γ δ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
  [MeasurableSpace δ]
open MeasureTheory ProbabilityTheory Function Set
open ProbabilityTheory
universe u u' v
variable {Ω Ω' α ι β β' T : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
  {mβ : MeasurableSpace β} {μ : Measure Ω} {ν : Measure Ω'} {f g : Ω
    → β} {f' g' : Ω' → β}
variable [MeasurableSpace α] [MeasurableSpace β]
namespace ProbabilityTheory
theorem _root_.solution {X : Ω → α} (hX : Measurable X) {f : α → β} (hf : Measurable f)
    (μ : Measure Ω) : IdentDistrib f (f ∘ X) (μ.map X) μ where
  aemeasurable_fst := hf.aemeasurable
  aemeasurable_snd := (hf.comp hX).aemeasurable
  map_eq := map_map hf hX
end ProbabilityTheory
