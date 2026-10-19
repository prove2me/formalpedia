-- Prove2me | solution 1 for SoficGroups.KunRootedIndicatorCrossing.norm_average_normalizedPairDisplacement_of_model
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:56.693907+00:00
-- url     : https://prove2.me/submissions/069d1ee3-35d5-417c-b8b0-d78ef3b93f3d

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_norm_normalizedIndicatorDefect
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_average_normalizedIndicatorDisplacement
import Theorems.Thm_SoficGroups_KunRootedIndicatorCrossing_normalizedPairDisplacement_generator_of_model

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRootedIndicatorCrossing
universe u
open Filter
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRootedIndicatorCrossing
theorem _root_.solution
    {G ι V : Type*} [Group G] [Fintype ι] [Nonempty ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ)
    (σ : G → Equiv.Perm V) (s : ι → G)
    (hone : σ 1 = 1) (hgenerator : ∀ i, σ (s i) = p i)
    (hdefect : permutationMarkov p (indicatorVector f) ≠
      indicatorVector f) :
    ‖(Fintype.card ι : ℂ)⁻¹ •
      ∑ i, normalizedPairDisplacement p f σ (s i, 1)‖ = 1 := by
  simp_rw [normalizedPairDisplacement_generator_of_model
    p f σ s hone hgenerator]
  rw [average_normalizedIndicatorDisplacement,
    norm_normalizedIndicatorDefect p f hdefect]
end SoficGroups.KunRootedIndicatorCrossing
