-- Prove2me | solution 1 for ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism.dense_lcC
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T09:03:41.640345+00:00
-- url     : https://prove2.me/submissions/e218b98c-03c1-4744-85e4-1359aea76924

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
theorem _root_.solution (y₁ : ι → H₁) (C₁ : Submodule ℂ H₁) (h₁ : ∀ i, y₁ i ∈ C₁)
    (hd₁ : C₁ ≤ (Submodule.span ℂ (Set.range y₁)).topologicalClosure) : DenseRange (lcC y₁ C₁ h₁) := by
  intro x
  rw [Topology.IsInducing.subtypeVal.closure_eq_preimage_closure_image]
  show (x : H₁) ∈ closure (Subtype.val '' Set.range (lcC y₁ C₁ h₁))
  have he : Subtype.val '' Set.range (lcC y₁ C₁ h₁) = (Submodule.span ℂ (Set.range y₁) : Set H₁) := by
    rw [← Set.range_comp, ← Finsupp.range_linearCombination, LinearMap.coe_range]
    rfl
  rw [he, ← Submodule.topologicalClosure_coe]
  exact hd₁ x.2
end ReciprocityTheory.ChartRestriction.DS.KTypeIsomorphism
