-- Prove2me | solution 1 for ProbabilityTheory.IdentDistrib.comp_left
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:18.336941+00:00
-- url     : https://prove2.me/submissions/ce42a459-c2fe-4f8d-98df-6bc18ce2e7f2

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_identDistrib_comp_left

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
namespace _root_.ProbabilityTheory.IdentDistrib
theorem _root_.solution
    {i : δ → α} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ,
  a ∈ range i)
    (hf : Measurable f) (hfg : IdentDistrib f g μ ν) : IdentDistrib (f ∘ i) g (μ.comap i) ν :=
  (identDistrib_comp_left hi hi' hf).trans hfg
end _root_.ProbabilityTheory.IdentDistrib
end ProbabilityTheory
