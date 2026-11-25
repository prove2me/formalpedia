-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kd_prod_bounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T12:32:01.585326+00:00
-- url     : https://prove2.me/submissions/ad418b5d-d6f8-45dd-8ede-6b6c2ffb977f

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_KDensC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_finite
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_le
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_ge
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_prod

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
variable {E₁ E₂ X₁ X₂ : Type*} [TopologicalSpace E₁] [PolishSpace E₁] [MeasurableSpace E₁] [BorelSpace E₁]
  [TopologicalSpace E₂] [PolishSpace E₂] [MeasurableSpace E₂] [BorelSpace E₂]
  [TopologicalSpace X₁] [T2Space X₁] [MeasurableSpace X₁] [BorelSpace X₁] [SecondCountableTopology X₁]
  [TopologicalSpace X₂] [T2Space X₂] [MeasurableSpace X₂] [BorelSpace X₂] [SecondCountableTopology X₂]
namespace ReciprocityTheory.ChartRestriction.DS
theorem _root_.solution {m₁ : Measure X₁} {m₂ : Measure X₂} [IsFiniteMeasure m₁] [IsFiniteMeasure m₂]
    (lam₁ : Measure E₁) (lam₂ : Measure E₂) [SigmaFinite lam₁] [SigmaFinite lam₂]
    {f₁ : E₁ → X₁} {f₂ : E₂ → X₂} {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : MeasurableSet U₁)
    (hU₂ : MeasurableSet U₂) (hf₁ : ContinuousOn f₁ U₁) (hf₂ : ContinuousOn f₂ U₂) (hi₁ : InjOn f₁ U₁)
    (hi₂ : InjOn f₂ U₂) (c₁ d₁ c₂ d₂ : ℝ≥0∞)
    (h₁ : ∀ A ⊆ U₁, MeasurableSet A → m₁ (f₁ '' A) ≤ c₁ * lam₁ A ∧ d₁ * lam₁ A ≤ m₁ (f₁ '' A))
    (h₂ : ∀ A ⊆ U₂, MeasurableSet A → m₂ (f₂ '' A) ≤ c₂ * lam₂ A ∧ d₂ * lam₂ A ≤ m₂ (f₂ '' A))
    {B : Set (E₁ × E₂)} (hB : MeasurableSet B) (hBU : B ⊆ U₁ ×ˢ U₂) :
    (m₁.prod m₂) (Prod.map f₁ f₂ '' B) ≤ c₁ * c₂ * (lam₁.prod lam₂) B ∧
      d₁ * d₂ * (lam₁.prod lam₂) B ≤ (m₁.prod m₂) (Prod.map f₁ f₂ '' B) := by
  have := kdNu_finite (m := m₁) hU₁ hf₁ hi₁
  have := kdNu_finite (m := m₂) hU₂ hf₂ hi₂
  have e : (m₁.prod m₂) (Prod.map f₁ f₂ '' B) = ((kdNu m₁ f₁ U₁).prod (kdNu m₂ f₂ U₂)) B := by
    rw [kdNu_prod hU₁ hU₂ hf₁ hf₂ hi₁ hi₂,
      kdNu_apply (hU₁.prod hU₂) (hf₁.prodMap hf₂) (hi₁.prodMap hi₂) hB, inter_eq_left.2 hBU]
  have hs : ∀ a b : ℝ≥0∞,
      ((a • lam₁.restrict U₁).prod (b • lam₂.restrict U₂)) B = a * b * (lam₁.prod lam₂) B := by
    intro a b
    rw [Measure.prod_smul_left, Measure.prod_smul_right, Measure.prod_restrict, smul_smul,
      Measure.smul_apply, Measure.restrict_apply hB, inter_eq_left.2 hBU, smul_eq_mul]
  refine ⟨?_, ?_⟩
  · rw [e, ← hs c₁ c₂]
    exact Measure.le_iff'.1 (Measure.prod_mono
      (kdNu_le hU₁ hf₁ hi₁ lam₁ c₁ fun A hA hm => (h₁ A hA hm).1)
      (kdNu_le hU₂ hf₂ hi₂ lam₂ c₂ fun A hA hm => (h₂ A hA hm).1)) B
  · rw [e, ← hs d₁ d₂]
    exact Measure.le_iff'.1 (Measure.prod_mono
      (kdNu_ge hU₁ hf₁ hi₁ lam₁ d₁ fun A hA hm => (h₁ A hA hm).2)
      (kdNu_ge hU₂ hf₂ hi₂ lam₂ d₂ fun A hA hm => (h₂ A hA hm).2)) B
end ReciprocityTheory.ChartRestriction.DS
