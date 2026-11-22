-- Prove2me | solution 1 for ProbabilityTheory.identDistrib_comp_fst
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:33.233842+00:00
-- url     : https://prove2.me/submissions/58fbdec6-7179-4809-8589-4a8c2f9c18df

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
    [IsProbabilityMeasure μ'] : IdentDistrib (X ∘ Prod.fst) X (μ.prod μ') μ where
  aemeasurable_fst := (hX.comp measurable_fst).aemeasurable
  aemeasurable_snd := hX.aemeasurable
  map_eq := by
    rw [← Measure.map_map hX measurable_fst, Measure.map_fst_prod]
    simp_all
end ProbabilityTheory
