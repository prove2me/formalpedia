-- Prove2me | solution 1 for SoficGroups.KunRootedWordPower.pairedDefectWordAverage_zero_eq_normalizedIndicatorDefect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/248e57e5-0c9f-4634-885c-8482f66b8938

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_average_normalizedIndicatorDisplacement
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_generator_of_model

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedWordPower
open Filter Topology
open SoficGroups.KunRootedIndicatorCrossing
open SoficGroups.KunThomInvariantOrthogonal
open scoped BigOperators ComplexConjugate ComplexOrder InnerProductSpace Pointwise
universe u v w
namespace SoficGroups.KunRootedWordPower
theorem _root_.solution
    {G ι V : Type*} [Group G] [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i) :
    pairedDefectWordAverage s
      (normalizedPairDisplacement p f σ) 0 =
        normalizedIndicatorDefect p f := by
  simp only [pairedDefectWordAverage, pairedWordAverage]
  simp_rw [normalizedPairDisplacement_generator_of_model
    p f σ s hone hgenerator]
  exact average_normalizedIndicatorDisplacement p f
end SoficGroups.KunRootedWordPower
