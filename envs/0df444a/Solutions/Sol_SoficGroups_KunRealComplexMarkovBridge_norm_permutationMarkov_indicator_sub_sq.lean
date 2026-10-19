-- Prove2me | solution 1 for SoficGroups.KunRealComplexMarkovBridge.norm_permutationMarkov_indicator_sub_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/416961f3-6690-46a4-bc4c-82c4fbcf79fb

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_indicatorVector_realMarkov
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_norm_indicatorVector_sub_sq

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRealComplexMarkovBridge
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) :
    ‖permutationMarkov p (indicatorVector f) - indicatorVector f‖ ^ 2 =
      ∑ x, (realMarkov p f x - f x) ^ 2 := by
  rw [← indicatorVector_realMarkov, norm_indicatorVector_sub_sq]
end SoficGroups.KunRealComplexMarkovBridge
