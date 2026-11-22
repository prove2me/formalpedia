-- Prove2me | solution 1 for ProbabilityTheory.AEMeasurable.piMk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:28:27.765802+00:00
-- url     : https://prove2.me/submissions/5569800d-7132-4c4b-ab97-0020fd249f0d

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
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
namespace _root_.ProbabilityTheory.AEMeasurable
theorem _root_.solution
    {I : Type*} [Countable I] {F : I → Ω → β} (hF : ∀ i,
  AEMeasurable (F i) μ) :
    AEMeasurable (fun x i => F i x) μ := by
  refine ⟨fun x i => (hF i).mk (F i) x,
    measurable_pi_lambda _ (fun i => (hF i).measurable_mk), ?_ ⟩
  filter_upwards [eventually_countable_forall.mpr (fun i ↦ (hF i).ae_eq_mk)] with ω hω
  ext i; exact hω i
end _root_.ProbabilityTheory.AEMeasurable
end ProbabilityTheory
