-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.Mult1.Fold.cutFold
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T12:12:39.643994+00:00
-- url     : https://prove2.me/submissions/812accf5-7974-4ebd-8b7c-5a61fa1d8b4d

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_MultiplicityOne_CutFold

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
namespace ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
theorem _root_.solution {α β E : Type*} [MeasurableSpace α] [MeasurableSpace β] [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (F G : β → α → α) (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    (hmp : ∀ᵐ s ∂ν, μ.map (F s) = μ) (hinv : ∀ᵐ p ∂(ν.prod μ), G p.1 (F p.1 p.2) = p.2)
    (b : α → ℝ) (hb : Measurable b) (hb0 : ∀ x, 0 ≤ b x)
    (h1 : ∀ᵐ x ∂μ, Integrable (fun s => b (G s x)) ν ∧ ∫ s, b (G s x) ∂ν = 1)
    (φ : α → E) (hφ : Integrable φ μ) :
    Integrable (fun p : β × α => b p.2 • φ (F p.1 p.2)) (ν.prod μ) ∧
      ∫ x, φ x ∂μ = ∫ x, b x • ∫ s, φ (F s x) ∂ν ∂μ := by
  have hΦ : MeasurePreserving (fun p : β × α => (p.1, F p.1 p.2)) (ν.prod μ) (ν.prod μ) :=
    (MeasurePreserving.id ν).skew_product hF hmp
  have hbG : Measurable fun q : β × α => b (G q.1 q.2) := hb.comp hG
  have hHm : AEStronglyMeasurable (fun q : β × α => b (G q.1 q.2) • φ q.2) (ν.prod μ) :=
    hbG.aestronglyMeasurable.smul hφ.1.comp_snd
  have hHi : Integrable (fun q : β × α => b (G q.1 q.2) • φ q.2) (ν.prod μ) := by
    rw [integrable_prod_iff' hHm]
    constructor
    · filter_upwards [h1] with y hy
      exact hy.1.smul_const (φ y)
    · refine hφ.norm.congr ?_
      filter_upwards [h1] with y hy
      show ‖φ y‖ = ∫ s, ‖b (G s y) • φ y‖ ∂ν
      have hn : ∀ s, ‖b (G s y) • φ y‖ = b (G s y) * ‖φ y‖ := fun s => by
        rw [norm_smul, Real.norm_of_nonneg (hb0 _)]
      simp only [hn]
      rw [integral_mul_const, hy.2, one_mul]
  have hcomp : (fun p : β × α => b p.2 • φ (F p.1 p.2)) =ᵐ[ν.prod μ]
      ((fun q : β × α => b (G q.1 q.2) • φ q.2) ∘ fun p : β × α => (p.1, F p.1 p.2)) := by
    filter_upwards [hinv] with p hp
    simp only [Function.comp_apply, hp]
  have hint : Integrable (fun p : β × α => b p.2 • φ (F p.1 p.2)) (ν.prod μ) :=
    (hΦ.integrable_comp_of_integrable hHi).congr hcomp.symm
  refine ⟨hint, ?_⟩
  have e1 : (∫ x, b x • ∫ s, φ (F s x) ∂ν ∂μ) = ∫ p, b p.2 • φ (F p.1 p.2) ∂(ν.prod μ) := by
    rw [integral_prod_symm _ hint]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    exact (integral_smul (b x) fun s => φ (F s x)).symm
  have hm : AEStronglyMeasurable (fun q : β × α => b (G q.1 q.2) • φ q.2)
      (Measure.map (fun p : β × α => (p.1, F p.1 p.2)) (ν.prod μ)) := by
    rw [hΦ.map_eq]
    exact hHm
  have e2 : (∫ p, b p.2 • φ (F p.1 p.2) ∂(ν.prod μ)) =
      ∫ q, b (G q.1 q.2) • φ q.2 ∂(ν.prod μ) := by
    rw [integral_congr_ae hcomp]
    calc ∫ p, ((fun q : β × α => b (G q.1 q.2) • φ q.2) ∘
            fun p : β × α => (p.1, F p.1 p.2)) p ∂(ν.prod μ)
        = ∫ q, b (G q.1 q.2) • φ q.2
            ∂(Measure.map (fun p : β × α => (p.1, F p.1 p.2)) (ν.prod μ)) :=
          (integral_map hΦ.measurable.aemeasurable hm).symm
      _ = ∫ q, b (G q.1 q.2) • φ q.2 ∂(ν.prod μ) := by rw [hΦ.map_eq]
  have e3 : (∫ q, b (G q.1 q.2) • φ q.2 ∂(ν.prod μ)) = ∫ y, φ y ∂μ := by
    rw [integral_prod_symm _ hHi]
    refine integral_congr_ae ?_
    filter_upwards [h1] with y hy
    show ∫ s, b (G s y) • φ y ∂ν = φ y
    rw [integral_smul_const, hy.2, one_smul]
  rw [e1, e2, e3]
end ReciprocityTheory.ChartRestriction.DS.Mult1.Fold
