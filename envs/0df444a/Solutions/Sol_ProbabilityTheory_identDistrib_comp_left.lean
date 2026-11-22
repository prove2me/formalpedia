-- Prove2me | solution 1 for ProbabilityTheory.identDistrib_comp_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:25:45.086096+00:00
-- url     : https://prove2.me/submissions/e98157b6-deb7-48d4-9c37-fc5104300a27

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
open ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}
namespace ProbabilityTheory
theorem _root_.solution {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ,
  a ∈ range i)
    (hf : Measurable f) : IdentDistrib (f ∘ i) f (μ.comap i) μ where
  aemeasurable_fst := (hf.comp hi.measurable).aemeasurable
  aemeasurable_snd := hf.aemeasurable
  map_eq := by rw [← Measure.map_map hf hi.measurable, hi.map_comap,
    restrict_eq_self_of_ae_mem hi']
end ProbabilityTheory
