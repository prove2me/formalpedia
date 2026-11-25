-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.norm_lc
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T12:16:28.278208+00:00
-- url     : https://prove2.me/submissions/247fee4e-335e-477f-a4b5-75b30b6bfc70

import Mathlib.Analysis.Normed.Operator.Extend
import Mathlib.Analysis.InnerProductSpace.Subspace
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_DiscreteSeriesExistence_PropsEquivA
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_KTypeIsomorphism_inner_lc

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
    (hI : ∀ i j, inner ℂ (y₂ i) (y₂ j) = inner ℂ (y₁ i) (y₁ j)) (f : ι →₀ ℂ) :
    ‖Finsupp.linearCombination ℂ y₂ f‖ = ‖Finsupp.linearCombination ℂ y₁ f‖ := by
  rw [@norm_eq_sqrt_re_inner ℂ, @norm_eq_sqrt_re_inner ℂ, inner_lc y₁ y₂ hI]
end ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
