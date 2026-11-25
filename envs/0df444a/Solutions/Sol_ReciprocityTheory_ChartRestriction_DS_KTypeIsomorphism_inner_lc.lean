-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.inner_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T12:11:15.707743+00:00
-- url     : https://prove2.me/submissions/952acea1-e4e8-4801-bf1c-ae902569db1a

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_PropsEquivA

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
namespace ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
theorem _root_.solution (y₁ : ι → H₁) (y₂ : ι → H₂)
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j)) (f f' : ι →₀ ℂ) :
    inner ℂ (Finsupp.linearCombination ℂ y₂ f) (Finsupp.linearCombination ℂ y₂ f') =
      inner ℂ (Finsupp.linearCombination ℂ y₁ f) (Finsupp.linearCombination ℂ y₁ f') := by
  simp only [Finsupp.linearCombination_apply, Finsupp.sum, sum_inner, inner_sum, inner_smul_left,
    inner_smul_right, hI]
end ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
