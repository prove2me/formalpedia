-- Prove2me | solution 1 for SoficGroups.SourceGeneration.prefixElementaryGroup_le_of_hub
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/d16ce910-4db2-4e4c-9eaa-e9f72ff0c73a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_prefixElementaryUnit_mem_of_two_step

set_option autoImplicit true
noncomputable section
open SoficGroups
open Filter Topology
universe u v w
open scoped Pointwise commutatorElement symmDiff
open SoficGroups.SourceGeneration
open scoped commutatorElement
namespace SoficGroups.SourceGeneration
theorem _root_.solution
    {ι : Type*} [DecidableEq ι] (E : BinaryPrefixCode ι)
    (H : Subgroup BinaryLeavittˣ) (k : ι)
    (hto : ∀ (i : ι) (h : i ≠ k) (a : BinaryLeavitt),
      prefixElementaryUnit E i k h a ∈ H)
    (hfrom : ∀ (j : ι) (h : k ≠ j) (a : BinaryLeavitt),
      prefixElementaryUnit E k j h a ∈ H) :
    prefixElementaryGroup E ≤ H := by
  rw [prefixElementaryGroup, Subgroup.closure_le]
  rintro _ ⟨i, j, hij, a, rfl⟩
  by_cases hi : i = k
  · subst k
    exact hfrom j hij a
  by_cases hj : j = k
  · subst k
    exact hto i hij a
  exact prefixElementaryUnit_mem_of_two_step E H i k j
    hi (Ne.symm hj) hij a (hto i hi a) (hfrom j (Ne.symm hj) 1)
end SoficGroups.SourceGeneration
