-- Prove2me | solution 1 for ProbabilityTheory.identDistrib_of_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:37:30.40411+00:00
-- url     : https://prove2.me/submissions/2ed89616-665a-4b78-a93b-fda848dc58ef

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_mul
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
variable [MeasurableSpace α] [MeasurableSpace β]
namespace ProbabilityTheory
theorem _root_.solution {X : Ω → α} {Y : Ω' → α} {μ : T → Measure Ω}
    {μ' : T → Measure Ω'} {w : T
      → ENNReal} (s : Finset T) (hX : Measurable X) (hY : Measurable Y)
    (h_ident : ∀ y, w y ≠ 0 → IdentDistrib X Y (μ y) (μ' y)) :
    IdentDistrib X Y (∑ y ∈ s, (w y) • (μ y)) (∑ y ∈ s, (w y) • (μ' y)) where
  aemeasurable_fst := hX.aemeasurable
  aemeasurable_snd := hY.aemeasurable
  map_eq := by
    rw [← Measure.mapₗ_apply_of_measurable hX, ← Measure.mapₗ_apply_of_measurable hY]
    simp only [_root_.map_sum, map_smul]
    congr with y E _
    rcases eq_or_ne (w y) 0 with hy | hy
    · simp [hy]
    congr 3
    rw [Measure.mapₗ_apply_of_measurable hX, Measure.mapₗ_apply_of_measurable hY]
    exact (h_ident y hy).map_eq
end ProbabilityTheory
