-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.gns_extend
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:21:59.30758+00:00
-- url     : https://prove2.me/submissions/9c0fe85b-9cff-49ae-a464-ecdf0b802c1f

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_PropsEquivA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_KTypeIsomorphism_norm_lc
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
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j))
    (C₁ : Submodule ℂ H₁) (C₂ : Submodule ℂ H₂) (hC₁ : IsClosed (C₁ : Set H₁)) (hC₂ : IsClosed (C₂ : Set H₂))
    (h₁ : ∀ i, y₁ i ∈ C₁) (h₂ : ∀ i, y₂ i ∈ C₂)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure)
    (hd₂ : C₂ ≤ (Submodule.span ℂ (Set.range y₂)).topologicalClosure) :
    ∃ U : C₁ ≃ₗᵢ[ℂ] C₂, ∀ (f : ι →₀ ℂ) (x : C₁), (x : H₁) = Finsupp.linearCombination ℂ y₁ f →
      ((U x : C₂) : H₂) = Finsupp.linearCombination ℂ y₂ f := by
  have : CompleteSpace C₁ := hC₁.completeSpace_coe
  have : CompleteSpace C₂ := hC₂.completeSpace_coe
  have hn : ∀ f, ‖lcC y₂ C₂ h₂ ((LinearEquiv.refl ℂ (ι →₀ ℂ)) f)‖ = ‖lcC y₁ C₁ h₁ f‖ := by
    intro f
    show ‖(lcC y₂ C₂ h₂ f : H₂)‖ = ‖(lcC y₁ C₁ h₁ f : H₁)‖
    exact norm_lc y₁ y₂ hI f
  refine ⟨(LinearEquiv.refl ℂ (ι →₀ ℂ)).extendOfIsometry (lcC y₁ C₁ h₁) (lcC y₂ C₂ h₂)
    (dense_lcC y₁ C₁ h₁ hd₁) (dense_lcC y₂ C₂ h₂ hd₂) hn, ?_⟩
  intro f x hx
  have hx' : x = lcC y₁ C₁ h₁ f := Subtype.ext hx
  subst hx'
  rw [LinearEquiv.extendOfIsometry_eq]
  rfl
end ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
