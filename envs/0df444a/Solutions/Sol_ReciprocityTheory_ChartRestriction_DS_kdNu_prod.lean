-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.kdNu_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:24:56.986919+00:00
-- url     : https://prove2.me/submissions/3e8aa1e6-50c8-4350-8703-b55e499605cc

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_FormalDegree_HaarVolumes_KDensC
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_apply
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_kdNu_finite

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
    {f₁ : E₁ → X₁} {f₂ : E₂ → X₂} {U₁ : Set E₁} {U₂ : Set E₂} (hU₁ : MeasurableSet U₁)
    (hU₂ : MeasurableSet U₂) (hf₁ : ContinuousOn f₁ U₁) (hf₂ : ContinuousOn f₂ U₂) (hi₁ : InjOn f₁ U₁)
    (hi₂ : InjOn f₂ U₂) :
    (kdNu m₁ f₁ U₁).prod (kdNu m₂ f₂ U₂) = kdNu (m₁.prod m₂) (Prod.map f₁ f₂) (U₁ ×ˢ U₂) := by
  have := kdNu_finite (m := m₁) hU₁ hf₁ hi₁
  have := kdNu_finite (m := m₂) hU₂ hf₂ hi₂
  refine Measure.prod_eq fun s t hs ht => ?_
  rw [kdNu_apply (hU₁.prod hU₂) (hf₁.prodMap hf₂) (hi₁.prodMap hi₂) (hs.prod ht),
    kdNu_apply hU₁ hf₁ hi₁ hs, kdNu_apply hU₂ hf₂ hi₂ ht, prod_inter_prod, prodMap_image_prod,
    Measure.prod_prod]
end ReciprocityTheory.ChartRestriction.DS
