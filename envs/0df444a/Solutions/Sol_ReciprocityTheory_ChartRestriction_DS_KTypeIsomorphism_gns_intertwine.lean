-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.gns_intertwine
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:06:56.294069+00:00
-- url     : https://prove2.me/submissions/4e66a808-02a6-4d7a-a5cc-2fe3a336cfc4

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_PropsEquivA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_KTypeIsomorphism_dense_lcC

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Matrix
open ReciprocityTheory ReciprocityTheory.ChartRestriction ReciprocityTheory.ChartRestriction.DS
open ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
variable {ι : Type*} {H₁ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  {H₂ : Type*} [NormedAddCommGroup H₂] [InnerProductSpace ℂ H₂]
variable [CompleteSpace H₁] [CompleteSpace H₂]
namespace ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
theorem _root_.solution (y₁ : ι → H₁) (y₂ : ι → H₂)
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (U : C₁ ≃ₗᵢ[ℂ] C₂) (hU : ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f)
    (T₁ : H₁ →L[ℂ] H₁) (T₂ : H₂ →L[ℂ] H₂) (τ : ι → ι) (hT₁ : ∀ i, T₁ (y₁ i) = y₁ (τ i))
    (hT₂ : ∀ i, T₂ (y₂ i) = y₂ (τ i)) (hTC : ∀ x ∈ C₁, T₁ x ∈ C₁) :
    ∀ x y : C₁, (x : H₁) = T₁ (y : H₁) → ((U x : C₂) : H₂) = T₂ ((U y : C₂) : H₂) := by
  let R : C₁ →L[ℂ] C₁ := (T₁.comp C₁.subtypeL).codRestrict C₁ (fun y => hTC _ y.2)
  let A : C₁ →L[ℂ] H₂ := C₂.subtypeL.comp (U.toLinearIsometry.toContinuousLinearMap.comp R)
  let B : C₁ →L[ℂ] H₂ := T₂.comp (C₂.subtypeL.comp U.toLinearIsometry.toContinuousLinearMap)
  have hAB : (A : C₁ → H₂) = B := by
    refine (dense_lcC y₁ C₁ h₁ hd₁).equalizer A.continuous B.continuous (funext fun f => ?_)
    show ((U (R (lcC y₁ C₁ h₁ f)) : C₂) : H₂) = T₂ ((U (lcC y₁ C₁ h₁ f) : C₂) : H₂)
    have hR : ((R (lcC y₁ C₁ h₁ f) : C₁) : H₁) =
        Finsupp.linearCombination ℂ y₁ (Finsupp.mapDomain τ f) := by
      show T₁ (Finsupp.linearCombination ℂ y₁ f) = _
      rw [Finsupp.linearCombination_mapDomain]
      have := Finsupp.apply_linearCombination ℂ T₁.toLinearMap y₁ f
      simp only [ContinuousLinearMap.coe_coe] at this
      rw [this, show (⇑T₁ ∘ y₁) = y₁ ∘ τ from funext hT₁]
    rw [hU _ _ hR, hU f _ rfl, Finsupp.linearCombination_mapDomain]
    have := Finsupp.apply_linearCombination ℂ T₂.toLinearMap y₂ f
    simp only [ContinuousLinearMap.coe_coe] at this
    rw [this, show (⇑T₂ ∘ y₂) = y₂ ∘ τ from funext hT₂]
  intro x y hxy
  have hx : x = R y := Subtype.ext hxy
  subst hx
  exact congrFun hAB y
end ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
