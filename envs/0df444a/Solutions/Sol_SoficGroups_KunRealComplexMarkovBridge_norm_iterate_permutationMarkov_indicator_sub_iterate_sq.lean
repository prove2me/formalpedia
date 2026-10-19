-- Prove2me | solution 1 for SoficGroups.KunRealComplexMarkovBridge.norm_iterate_permutationMarkov_indicator_sub_iterate_sq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:59.059963+00:00
-- url     : https://prove2.me/submissions/c9bcdeeb-34ba-467f-852e-19a55ce19efe

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_indicatorVector_iterate_realMarkov
import Theorems.Thm_SoficGroups_KunRealComplexMarkovBridge_norm_indicatorVector_sub_sq

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.KunRealComplexMarkovBridge
open scoped BigOperators ComplexOrder InnerProductSpace Topology
namespace SoficGroups.KunRealComplexMarkovBridge
theorem _root_.solution
    {ι V : Type*} [Fintype ι] [Fintype V]
    (p : ι → Equiv.Perm V) (f : V → ℝ) (k : ℕ) :
    ‖((permutationMarkov p)^[k + 1]) (indicatorVector f) -
        ((permutationMarkov p)^[k]) (indicatorVector f)‖ ^ 2 =
      ∑ x, ((((realMarkov p)^[k + 1]) f) x -
        (((realMarkov p)^[k]) f) x) ^ 2 := by
  rw [← indicatorVector_iterate_realMarkov,
    ← indicatorVector_iterate_realMarkov,
    norm_indicatorVector_sub_sq]
end SoficGroups.KunRealComplexMarkovBridge
