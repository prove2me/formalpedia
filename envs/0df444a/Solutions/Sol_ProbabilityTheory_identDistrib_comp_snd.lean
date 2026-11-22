-- Prove2me | solution 1 for ProbabilityTheory.identDistrib_comp_snd
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:33.634471+00:00
-- url     : https://prove2.me/submissions/56813b6e-7a00-4d97-9aa7-431c8edb8a27

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_mul
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_ProbabilityTheory_iIndepFun_prod
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] ProbabilityTheory.indepFun_zero_measure


attribute [local simp] ProbabilityTheory.identDistrib_id

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
theorem _root_.solution {X : Ω
  → α} (hX : Measurable X) (μ : Measure Ω) (μ' : Measure Ω')
  [SigmaFinite μ] [IsProbabilityMeasure μ'] :
    IdentDistrib (X ∘ Prod.snd) X (μ'.prod μ) μ where
  aemeasurable_fst := (hX.comp measurable_snd).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [← Measure.map_map hX measurable_snd, Measure.map_snd_prod]
    simp_all
end ProbabilityTheory
