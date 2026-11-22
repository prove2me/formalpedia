-- Prove2me | solution 1 for P2M_ProbabilityTheory_condIndep_copies__84a4bd00618a
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:45:02.739861+00:00
-- url     : https://prove2.me/submissions/58a19b58-cc3a-4541-a911-a8a6cfdb5294

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Theorems.Thm_ProbabilityTheory_CondIndepFun_comp_right
public import Theorems.Thm_ProbabilityTheory_condIndep_copies
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_comp_left
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_comp_right
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_IndepFun_comp_right
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_indepFun_zero_measure
public import Theorems.Thm_prod_eq
attribute [local simp] MeasureTheory.Measure.pi_eval_preimage
attribute [local simp] MeasureTheory.Measure.pi_pi_set
attribute [local simp] ProbabilityTheory.identDistrib_id
attribute [local simp] ProbabilityTheory.indepFun_zero_measure
attribute [local simp] prod_eq



set_option autoImplicit true
@[expose] public section
public section
open MeasureTheory Measure Set
open scoped ENNReal ZhangYeungPFR
open ProbabilityTheory
universe u
variable {Ω : Type*} {α β :
  Type u} [MeasurableSpace Ω] [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSingletonClass β]
variable [Countable β]
open Function Set Measure
namespace ProbabilityTheory
namespace _root_.ProbabilityTheory
theorem _root_.solution
    (X : Ω → α) (Y : Ω → β) (hX : Measurable X) (hY : Measurable Y)
    [FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] (p : α → β → Prop)
    (hp : Measurable (uncurry p)) (hp' : ∀ᵐ ω ∂μ, p (X ω) (Y ω)) :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω'
      → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
       IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ ∧ (∀ ω,
         p (X₁ ω) (Y' ω)) ∧ (∀ ω, p (X₂ ω) (Y' ω)) := by
  obtain ⟨Ω', _, X₁, X₂, Y', ν, _, hX₁, hX₂, hY', hXY, hXY₁, hXY₂⟩ :=
    condIndep_copies X Y hX hY μ
  let i := Subtype.val (p := fun ω ↦ p (X₁ ω) (Y' ω) ∧ p (X₂ ω) (Y' ω))
  have hi : MeasurableEmbedding i := MeasurableEmbedding.subtype_coe
    ((hp.comp <| hX₁.prodMk hY').and <| hp.comp <| hX₂.prodMk hY').setOf
  have hi' : ∀ᵐ ω ∂ν, ω ∈ range i := by
    simp only [i, mem_ofPred_eq, Subtype.range_coe_subtype, Filter.eventually_and]
    exact ⟨hXY₁.symm.ae_snd (p := uncurry p) hp.setOf hp',
      hXY₂.symm.ae_snd (p := uncurry p) hp.setOf hp'⟩
  refine ⟨{ω // p (X₁ ω) (Y' ω) ∧ p (X₂ ω) (Y' ω)}, inferInstance, X₁ ∘ (↑),
    X₂ ∘ (↑), Y' ∘ (↑),
    ν.comap (↑), ?_, hX₁.comp measurable_subtype_coe, hX₂.comp measurable_subtype_coe,
    hY'.comp measurable_subtype_coe, ?_, ?_, ?_, fun ω ↦ ω.2.1, fun ω ↦ ω.2.2⟩
  · exact hi.isProbabilityMeasure_comap hi'
  · exact hXY.comp_right hi hi' hX₁ hX₂ hY'
  · exact hXY₁.comp_left hi hi' <| hX₁.prodMk hY'
  · exact hXY₂.comp_left hi hi' <| hX₂.prodMk hY'
end _root_.ProbabilityTheory
end ProbabilityTheory
