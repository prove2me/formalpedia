-- Prove2me | solution 1 for ProbabilityTheory.map_uniformOn_apply
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:40:18.603597+00:00
-- url     : https://prove2.me/submissions/e7402ccf-e8d8-4ae4-8968-b9f00d153279

module
public import Mathlib.Probability.UniformOn
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Data_Set_Card
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_UniformOn
public import Theorems.Thm_ProbabilityTheory_uniformOn_of_infinite
public import Theorems.Thm_ProbabilityTheory_uniformOn_apply

set_option autoImplicit true
@[expose] public section
public section
open Function MeasureTheory Measure
open ProbabilityTheory
variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
  [MeasurableSpace Ω'] [MeasurableSingletonClass Ω'] {s t : Set Ω} {x : Ω}
namespace ProbabilityTheory
theorem _root_.solution {f : Ω → Ω'} (hmes : Measurable f) (hf : Injective f) {t : Set Ω'}
    (ht : MeasurableSet t) :
    (uniformOn s).map f t = uniformOn (f '' s) t := by
  obtain hs | hs := s.infinite_or_finite
  · simp [uniformOn_of_infinite, hs, hs.image hf.injOn]
  · rw [map_apply hmes ht, uniformOn_apply hs, uniformOn_apply (hs.image _),
      Nat.card_image_of_injective hf, ← Nat.card_image_of_injective hf, Set.image_inter_preimage]
end ProbabilityTheory
