-- Prove2me | solution 1 for ProbabilityTheory.condIndep_copies
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T14:38:20.990334+00:00
-- url     : https://prove2.me/submissions/269aaacf-81fc-46b6-8ff4-31388a9721cb

module
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_IdentDistrib
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_Pair
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_Defs
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_FiniteRange_ConditionalProbability
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_Mathlib_Probability_Independence_Basic
public import Definitions.Def_LeanPool_ZhangYeungInequality_PFR_ForMathlib_ConditionalIndependence
public import Theorems.Thm_ProbabilityTheory_condIndepFun_iff
public import Theorems.Thm_MeasureTheory_Measure_pi_eval_preimage
public import Theorems.Thm_MeasureTheory_Measure_pi_pi_set
public import Theorems.Thm_P2M_ProbabilityTheory_sum_meas_smul_cond_fiber__96388389e218
public import Theorems.Thm_ProbabilityTheory_IdentDistrib_prodMk
public import Theorems.Thm_ProbabilityTheory_iIndepFun_prod
public import Theorems.Thm_ProbabilityTheory_identDistrib_comp_fst
public import Theorems.Thm_ProbabilityTheory_identDistrib_comp_snd
public import Theorems.Thm_ProbabilityTheory_identDistrib_id
public import Theorems.Thm_ProbabilityTheory_identDistrib_map
public import Theorems.Thm_ProbabilityTheory_identDistrib_of_sum
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
    [finY : FiniteRange Y] (μ : Measure Ω) [IsProbabilityMeasure μ] :
    ∃ (Ω' : Type u) (_ : MeasurableSpace Ω') (X₁ X₂ : Ω' → α) (Y' : Ω'
      → β) (ν : Measure Ω'),
      IsProbabilityMeasure ν ∧ Measurable X₁ ∧ Measurable X₂ ∧ Measurable Y' ∧
      CondIndepFun X₁ X₂ Y' ν ∧ IdentDistrib (⟨X₁, Y'⟩) (⟨X, Y⟩) ν μ ∧
      IdentDistrib (⟨X₂, Y'⟩) (⟨X, Y⟩) ν μ := by
  let m' := fun (y : β) ↦ ((μ[|Y ← y]).map X)
  let m := fun (y : β) ↦ ((m' y).prod (m' y)).prod (Measure.dirac y)
  let ν : Measure ((α × α) × β) := ∑ y ∈ finY.toFinset, ((μ (Y ⁻¹' {y})) • (m y))
  have h3' (y : β) : { ω : Ω | Y ω = y } ∈ ae (μ[|Y ← y]) := by
    rw [mem_ae_iff, ← cond_inter_self]
    · have : (Y ⁻¹' {y}) ∩ { ω : Ω | Y ω = y }ᶜ = ∅ := by
        ext _; simp
      simp [this]
    exact hY <| .singleton y
  have h3 (y : β) : IdentDistrib (fun ω ↦ (X ω, y)) (⟨X,
    Y⟩) (μ[|Y ← y]) (μ[|Y ← y]) := by
    apply IdentDistrib.of_ae_eq (hX.prodMk measurable_const).aemeasurable
    apply Filter.eventuallyEq_of_mem (h3' y)
    intro ω; simp only [mem_ofPred_eq, Prod.mk.injEq, true_and]; exact fun a ↦ id a.symm
  have h4 (y : β) : { ω : (α × α) × β| ω.2 = y } ∈ ae (m y) := by
    rw [mem_ae_iff]
    have : { ω : (α × α) × β | ω.2 = y}ᶜ = Prod.snd⁻¹' {y}ᶜ := by
      simp only [preimage_compl, compl_inj_iff]
      rfl
    rw [this, ← Measure.map_apply measurable_snd (MeasurableSet.singleton y).compl]
    simp [m]
  have h5 {y : β} (hy : μ (Y ⁻¹' {y}) ≠ 0) : IsProbabilityMeasure (m' y) := by
    have : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure hy
    exact Measure.isProbabilityMeasure_map hX.aemeasurable
  have h1 : ν.map Prod.snd = μ.map Y := by
    rw [← sum_meas_smul_cond_fiber' hY μ, ← Measure.mapₗ_apply_of_measurable measurable_snd,
      ← Measure.mapₗ_apply_of_measurable hY]
    simp only [_root_.map_sum, LinearMapClass.map_smul, ν]
    congr with y
    rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
    · simp [hy]
    have h6 : IsProbabilityMeasure (m' y) := h5 hy
    have h7 : IsProbabilityMeasure (μ[|Y ← y]) := cond_isProbabilityMeasure hy
    congr 3
    rw [Measure.mapₗ_apply_of_measurable measurable_snd, Measure.mapₗ_apply_of_measurable hY]
    simp only [map_snd_prod, measure_univ, one_smul, m]
    have := (μ[|Y ← y]).map_const y
    simp only [measure_univ, one_smul] at this; rw [← this]
    apply Measure.map_congr
    apply Filter.eventuallyEq_of_mem (h3' y)
    intro ω; simp only [mem_ofPred_eq]; exact fun a ↦ a.symm
  refine ⟨(α × α) × β, by infer_instance, fun ω ↦ ω.1.1, fun ω ↦ ω.1.2,
    fun ω ↦ ω.2, ν, ?_,
    measurable_fst.comp measurable_fst, measurable_snd.comp measurable_fst,
    measurable_snd, ?_, ?_, ?_⟩
  · constructor
    simp only [coe_finsetSum, Finset.sum_apply, ν]
    have : ∑ y ∈ finY.toFinset, μ (Y ⁻¹' {y}) * 1 = 1 := by
      simp only [mul_one]
      rw [sum_measure_preimage_singleton]
      · rw [← FiniteRange.range Y, preimage_range, measure_univ]
      · exact fun y _ ↦ hY <| .singleton y
    rw [← this]
    congr with y
    rcases eq_or_ne (μ (Y ⁻¹' {y})) 0 with hy | hy
    · simp [hy]
    have : IsProbabilityMeasure (m' y) := h5 hy
    simp
  · rw [condIndepFun_iff, ae_iff_of_countable]
    intro y hy
    have hy' : ν (Prod.snd⁻¹' {y}) = μ (Y ⁻¹' {y}) := by
      rw [← map_apply measurable_snd (by simp), ← map_apply hY <| .singleton y, h1]
    rw [h1] at hy
    have hy'' : μ (Y ⁻¹' {y}) ≠ 0 := by
      simp_all
    have h2 : ν[| Prod.snd⁻¹' {y}] = m y := by
      rw [Measure.ext_iff]
      intro E _
      rw [cond_apply (measurable_snd (by simp)), hy']
      have h3 : (m y) ((Prod.snd⁻¹' {y}) ∩ E) = (m y) E := by
        apply measure_congr
        apply inter_ae_eq_right_of_ae_eq_univ
        simp only [ae_eq_univ]
        rw [(show (Prod.snd⁻¹' {y})ᶜ = Prod.snd⁻¹' ({y}ᶜ) by rfl),
          ← map_apply measurable_snd (by simp)]
        simp [m]
      have h3' {x : β} (hx : x ≠ y) : (m x) ((Prod.snd⁻¹' {y}) ∩ E) = 0 := by
        apply measure_inter_null_of_null_left E
        rw [← Measure.map_apply measurable_snd (by simp), MeasureTheory.Measure.map_snd_prod]
        simp_all
      simp only [coe_finsetSum, coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, ν]
      rw [Finset.sum_eq_single_of_mem y ?_]
      · rw [h3, ← mul_assoc, ENNReal.inv_mul_cancel hy'', one_mul]
        finiteness
      · simp_all
      · rw [← Finset.mem_coe]
        convert FiniteRange.range Y ▸ Set.preimage_singleton_nonempty.mp
          (nonempty_of_measure_ne_zero hy'')
    rw [h2, indepFun_iff_map_prod_eq_prod_map_map]
    · let f : (α × α) × β → α × α := Prod.fst
      change ((m y).map f) = ((m y).map (Prod.fst ∘ f)).prod ((m y).map (Prod.snd ∘ f))
      have : IsProbabilityMeasure (m' y) := h5 hy''
      have : (m y).map f = (m' y).prod (m' y) := by simp [f, m]
      rw [← map_map measurable_fst measurable_fst, ← map_map measurable_snd measurable_fst,
        this]
      simp
    · exact (measurable_fst.comp measurable_fst).aemeasurable
    exact (measurable_snd.comp measurable_fst).aemeasurable
  · rw [← sum_meas_smul_cond_fiber' hY μ]
    refine identDistrib_of_sum _ ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
      (hX.prodMk hY) ?_
    intro y hy
    have h1 : IdentDistrib (fun ω ↦ (ω.1.1, ω.2)) (fun ω ↦ (ω.1.1, y)) (m y) (m y) := by
      refine .of_ae_eq ((measurable_fst.comp measurable_fst).prodMk measurable_snd).aemeasurable ?_
      apply Filter.eventuallyEq_of_mem (h4 y)
      intro _; simp
    have h2 : IdentDistrib (fun ω ↦ (ω.1.1, y)) (fun ω ↦ (X ω,
      y)) (m y) (μ[|Y ← y]) := by
      apply IdentDistrib.comp _ measurable_prodMk_right
      apply (identDistrib_comp_fst measurable_fst _ _).trans
      have : IsProbabilityMeasure ((μ[|Y ← y]).map X) := h5 hy
      apply (identDistrib_comp_fst measurable_id _ _).trans
      apply identDistrib_map hX measurable_id
    exact (h1.trans h2).trans (h3 y)
  rw [← sum_meas_smul_cond_fiber' hY μ]
  apply identDistrib_of_sum _ ((measurable_snd.comp measurable_fst).prodMk measurable_snd)
    (hX.prodMk hY)
  intro y hy
  have h1 : IdentDistrib (fun ω ↦ (ω.1.2, ω.2)) (fun ω ↦ (ω.1.2, y)) (m y) (m y) := by
    refine .of_ae_eq ((measurable_snd.comp measurable_fst).prodMk measurable_snd).aemeasurable ?_
    apply Filter.eventuallyEq_of_mem (h4 y)
    intro _; simp
  have h2 : IdentDistrib (fun ω ↦ (ω.1.2, y)) (fun ω ↦ (X ω, y)) (m y) (μ[|Y ← y]) := by
    apply IdentDistrib.comp _ measurable_prodMk_right
    apply (identDistrib_comp_fst measurable_snd _ _).trans
    have : IsProbabilityMeasure ((μ[|Y ← y]).map X) := h5 hy
    exact (identDistrib_comp_snd measurable_id _ _).trans (identDistrib_map hX measurable_id _)
  exact (h1.trans h2).trans (h3 y)
end _root_.ProbabilityTheory
end ProbabilityTheory
