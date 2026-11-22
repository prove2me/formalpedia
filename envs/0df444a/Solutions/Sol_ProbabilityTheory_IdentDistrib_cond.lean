-- Prove2me | solution 1 for ProbabilityTheory.IdentDistrib.cond
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:29:22.057887+00:00
-- url     : https://prove2.me/submissions/e5a3c48b-8476-4fe1-b241-2e010a5ae6de

module
public import Mathlib.Probability.IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_MeasureTheory_Constructions_Pi
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
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
    (hs : MeasurableSet s) (hf' : Measurable f') (hg' : Measurable g')
    (hfg : IdentDistrib (fun a ↦ (f a, f' a)) (fun b ↦ (g b, g' b)) μ ν) :
    IdentDistrib f g (μ[|f' ⁻¹' s]) (ν[|g' ⁻¹' s]) where
  aemeasurable_fst := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_fst).mono_ac
    cond_absolutelyContinuous
  aemeasurable_snd := (measurable_fst.aemeasurable.comp_aemeasurable hfg.aemeasurable_snd).mono_ac
    cond_absolutelyContinuous
  map_eq := by
    ext t ht
    rw [map_apply₀ (by exact
      (hfg.comp measurable_fst).aemeasurable_fst.mono_ac cond_absolutelyContinuous)
      ht.nullMeasurableSet, map_apply₀ (by exact
      (hfg.comp measurable_fst).aemeasurable_snd.mono_ac cond_absolutelyContinuous)
      ht.nullMeasurableSet, cond_apply (hg' hs), cond_apply (hf' hs)]
    congr
    · have hfs : (Prod.snd ∘ fun a ↦ (f a, f' a)) ⁻¹' s = f' ⁻¹' s := by
        ext a
        rfl
      have hgs : (Prod.snd ∘ fun b ↦ (g b, g' b)) ⁻¹' s = g' ⁻¹' s := by
        ext b
        rfl
      simpa [hfs, hgs, map_apply₀
          (hfg.comp measurable_snd).aemeasurable_fst hs.nullMeasurableSet,
          map_apply₀ (hfg.comp measurable_snd).aemeasurable_snd hs.nullMeasurableSet]
        using congr_fun (congr_arg (⇑) (hfg.comp measurable_snd).map_eq) s
    · rw [inter_comm, inter_comm (g' ⁻¹' _)]
      have hfts : (fun a ↦ (f a, f' a)) ⁻¹' (t ×ˢ s) = f ⁻¹' t ∩ f' ⁻¹' s := by
        ext a
        rfl
      have hgts : (fun b ↦ (g b, g' b)) ⁻¹' (t ×ˢ s) = g ⁻¹' t ∩ g' ⁻¹' s := by
        ext b
        rfl
      simpa [hfts, hgts, map_apply₀ hfg.aemeasurable_fst (ht.prod hs).nullMeasurableSet,
          map_apply₀ hfg.aemeasurable_snd (ht.prod hs).nullMeasurableSet]
        using congr_fun (congr_arg (⇑) hfg.map_eq) (t ×ˢ s)
end _root_.ProbabilityTheory.IdentDistrib
end ProbabilityTheory
