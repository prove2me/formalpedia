-- Prove2me | solution 1 for ProbabilityTheory.IdentDistrib.snd_id
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:43:56.072681+00:00
-- url     : https://prove2.me/submissions/bf31799f-2dae-4d2f-a518-91f6ae2f0e44

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_identDistrib_id_right
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
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
open ProbabilityTheory
variable {μ : Measure α} {ν : Measure β} {f f' : α → γ} {g g' : β → γ} {s : Set γ}
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.IdentDistrib
theorem _root_.solution
    {μ : Measure α} {ν : Measure β} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    IdentDistrib Prod.snd id (μ.prod ν) ν := by
  have : ν = (μ.prod ν).map Prod.snd := by simp
  nth_rewrite 2 [this]
  exact identDistrib_id_right measurable_snd.aemeasurable
end _root_.ProbabilityTheory.IdentDistrib
end ProbabilityTheory
