-- Prove2me | solution 1 for ProbabilityTheory.IdentDistrib.iprodMk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:44:16.070199+00:00
-- url     : https://prove2.me/submissions/1820150d-99da-4707-bb71-d0b3217a8458

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_AEMeasurable_piMk
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
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
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.IdentDistrib
theorem _root_.solution
    {I : Type*} [Finite I] {F : I → Ω → β} {F' : I → Ω' → β}
    (hFF' : ∀ i, IdentDistrib (F i) (F' i) μ ν) (hμ : IsProbabilityMeasure μ)
    (hν : IsProbabilityMeasure ν) (h : iIndepFun F μ) (h' : iIndepFun F' ν) :
    IdentDistrib (fun x i ↦ F i x) (fun x i ↦ F' i x) μ ν where
  aemeasurable_fst := by
    apply AEMeasurable.piMk
    intro i; exact (hFF' i).aemeasurable_fst
  aemeasurable_snd := by
    apply AEMeasurable.piMk
    intro i; exact (hFF' i).aemeasurable_snd
  map_eq := by
    cases nonempty_fintype I
    rw [iIndepFun_iff_map_fun_eq_pi_map] at h h'
    · rw [h,h']
      congr
      ext i : 1
      exact (hFF' i).map_eq
    · intro i; exact (hFF' i).aemeasurable_snd
    intro i; exact (hFF' i).aemeasurable_fst
end _root_.ProbabilityTheory.IdentDistrib
end ProbabilityTheory
