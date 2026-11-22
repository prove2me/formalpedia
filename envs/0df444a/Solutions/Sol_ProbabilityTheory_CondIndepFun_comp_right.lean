-- Prove2me | solution 1 for ProbabilityTheory.CondIndepFun.comp_right
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:30:14.030578+00:00
-- url     : https://prove2.me/submissions/b8181124-d0be-4446-88cd-d8694bc57df2

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Theorems.Thm_ProbabilityTheory_condIndepFun_iff
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_comp_right
public import Theorems.Thm_ProbabilityTheory_IndepFun_comp_right


set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
open ProbabilityTheory
variable {Ω Ω' α β γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] [MeasurableSpace α]
  [MeasurableSpace β] [MeasurableSpace γ] {μ : Measure Ω} {f : Ω → α} {g : Ω
    → β} {h : Ω → γ}
variable [MeasurableSingletonClass γ]
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory.CondIndepFun
theorem _root_.solution {i : Ω'
  → Ω} (hi : MeasurableEmbedding i) (hi' : ∀ᵐ a ∂μ, a ∈ range i)
    (hf : Measurable f) (hg : Measurable g) (hh : Measurable h) (hfg : CondIndepFun f g h μ) :
    CondIndepFun (f ∘ i) (g ∘ i) (h ∘ i) (μ.comap i) := by
  rw [condIndepFun_iff] at hfg ⊢
  rw [← Measure.map_map hh hi.measurable, hi.map_comap, restrict_eq_self_of_ae_mem hi']
  refine hfg.mono <| fun c hc ↦ ?_
  rw [preimage_comp, ← comap_cond hi hi' <| hh <| .singleton _]
  exact IndepFun.comp_right hi (cond_absolutelyContinuous.ae_le hi') hf hg hc
end _root_.ProbabilityTheory.CondIndepFun
end ProbabilityTheory
