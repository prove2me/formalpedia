-- Prove2me | solution 1 for Tensorization.klDiv_prod_eq_add
-- status  : ACCEPTED   (prove)
-- author  : @Grace
-- created : 2026-06-23T02:56:06.333361+00:00
-- url     : https://prove2.me/submissions/3b370a28-69c5-44e7-a35c-2ed4935845dc

import Mathlib.InformationTheory.KullbackLeibler.ChainRule
import Mathlib.Probability.Kernel.Composition.MeasureCompProd
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym

open MeasureTheory InformationTheory ProbabilityTheory
open scoped ENNReal

set_option autoImplicit false

theorem solution {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    (μ ν : Measure α) (π ρ : Measure β)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    [IsProbabilityMeasure π] [IsProbabilityMeasure ρ] :
    klDiv (μ.prod π) (ν.prod ρ) = klDiv μ ν + klDiv π ρ := by
  -- KL is invariant under a measurable equivalence (specialized to product types)
  have klDiv_map_equiv : ∀ (e : (α × β) ≃ᵐ (β × α)) (μ' ν' : Measure (α × β))
      [SigmaFinite μ'] [SigmaFinite ν'],
      klDiv (μ'.map e) (ν'.map e) = klDiv μ' ν' := by
    intro e μ' ν' _ _
    have hemb : MeasurableEmbedding e := e.measurableEmbedding
    -- llr of the pushforwards
    have llr_map_equiv : (fun y ↦ llr (μ'.map e) (ν'.map e) y)
        =ᵐ[ν'.map e] fun y ↦ llr μ' ν' (e.symm y) := by
      have h := hemb.rnDeriv_map μ' ν'
      rw [Filter.EventuallyEq, hemb.ae_map_iff]
      filter_upwards [h] with x hx
      simp only [llr]
      rw [MeasurableEquiv.symm_apply_apply, hx]
    by_cases h_ac : μ' ≪ ν'
    swap
    · rw [klDiv_of_not_ac h_ac, klDiv_of_not_ac]
      intro hcon
      apply h_ac
      have hpb : (μ'.map e).map e.symm ≪ (ν'.map e).map e.symm := hcon.map e.symm.measurable
      have hid : ∀ θ : Measure (α × β), (θ.map e).map e.symm = θ := by
        intro θ
        rw [Measure.map_map e.symm.measurable e.measurable]
        have : (e.symm : (β × α) → (α × β)) ∘ (e : (α × β) → (β × α)) = id := by
          funext x; exact e.symm_apply_apply x
        rw [this, Measure.map_id]
      rwa [hid μ', hid ν'] at hpb
    · have h_ac' : μ'.map e ≪ ν'.map e := h_ac.map e.measurable
      have hcomp : ((fun y ↦ llr μ' ν' (e.symm y)) ∘ (e : (α × β) → (β × α))) = fun x ↦ llr μ' ν' x := by
        ext x; simp
      by_cases h_int : Integrable (llr μ' ν') μ'
      · have h_int' : Integrable (llr (μ'.map e) (ν'.map e)) (μ'.map e) := by
          rw [integrable_congr (llr_map_equiv.filter_mono h_ac'.ae_le)]
          rw [integrable_map_equiv e (fun y ↦ llr μ' ν' (e.symm y)), hcomp]
          exact h_int
        rw [klDiv_of_ac_of_integrable h_ac' h_int', klDiv_of_ac_of_integrable h_ac h_int]
        congr 1
        have h1 : ∫ y, llr (μ'.map e) (ν'.map e) y ∂(μ'.map e) = ∫ x, llr μ' ν' x ∂μ' := by
          rw [integral_congr_ae (llr_map_equiv.filter_mono h_ac'.ae_le)]
          rw [integral_map_equiv e (fun y ↦ llr μ' ν' (e.symm y))]
          simp
        have hreal : ∀ θ : Measure (α × β), (θ.map e).real Set.univ = θ.real Set.univ := by
          intro θ
          rw [measureReal_def, measureReal_def, Measure.map_apply e.measurable MeasurableSet.univ]
          simp
        rw [h1, hreal, hreal]
      · rw [klDiv_of_not_integrable h_int, klDiv_of_not_integrable]
        rw [integrable_congr (llr_map_equiv.filter_mono h_ac'.ae_le),
          integrable_map_equiv e (fun y ↦ llr μ' ν' (e.symm y)), hcomp]
        exact h_int
  -- tensorization in the first factor (chain rule with a constant kernel), specialized to the
  -- β-first / α-second product needed below after the coordinate swap
  have klDiv_prod_left : ∀ (μ₁ ν₁ : Measure β) (π₁ : Measure α)
      [IsFiniteMeasure μ₁] [IsFiniteMeasure ν₁] [IsProbabilityMeasure π₁],
      klDiv (μ₁.prod π₁) (ν₁.prod π₁) = klDiv μ₁ ν₁ := by
    intro μ₁ ν₁ π₁ _ _ _
    rw [← Measure.compProd_const (μ := μ₁) (ν := π₁),
      ← Measure.compProd_const (μ := ν₁) (ν := π₁)]
    exact klDiv_compProd_left μ₁ ν₁ (Kernel.const β π₁)
  -- tensorization in the second factor (swap + invariance)
  have klDiv_prod_right : ∀ (μ₁ : Measure α) (π₁ ρ₁ : Measure β)
      [IsProbabilityMeasure μ₁] [IsProbabilityMeasure π₁] [IsProbabilityMeasure ρ₁],
      klDiv (μ₁.prod π₁) (μ₁.prod ρ₁) = klDiv π₁ ρ₁ := by
    intro μ₁ π₁ ρ₁ _ _ _
    let e : (α × β) ≃ᵐ (β × α) := MeasurableEquiv.prodComm
    have hswapπ : (μ₁.prod π₁).map e = π₁.prod μ₁ := by
      rw [show (e : α × β → β × α) = Prod.swap from rfl, Measure.prod_swap]
    have hswapρ : (μ₁.prod ρ₁).map e = ρ₁.prod μ₁ := by
      rw [show (e : α × β → β × α) = Prod.swap from rfl, Measure.prod_swap]
    calc klDiv (μ₁.prod π₁) (μ₁.prod ρ₁)
        = klDiv ((μ₁.prod π₁).map e) ((μ₁.prod ρ₁).map e) :=
          (klDiv_map_equiv e (μ₁.prod π₁) (μ₁.prod ρ₁)).symm
      _ = klDiv (π₁.prod μ₁) (ρ₁.prod μ₁) := by rw [hswapπ, hswapρ]
      _ = klDiv π₁ ρ₁ := klDiv_prod_left π₁ ρ₁ μ₁
  -- assemble via the chain rule
  rw [← Measure.compProd_const (μ := μ) (ν := π), ← Measure.compProd_const (μ := ν) (ν := ρ)]
  rw [klDiv_compProd_eq_add μ ν (Kernel.const α π) (Kernel.const α ρ)]
  rw [Measure.compProd_const, Measure.compProd_const, klDiv_prod_right]
