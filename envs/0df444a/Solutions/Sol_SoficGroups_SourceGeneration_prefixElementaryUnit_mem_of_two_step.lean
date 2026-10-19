-- Prove2me | solution 1 for SoficGroups.SourceGeneration.prefixElementaryUnit_mem_of_two_step
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/ec135354-e341-4f82-a1cc-576a8fc54376

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_prefixElementaryUnit_commutator

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
    (H : Subgroup BinaryLeavittˣ) (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a : BinaryLeavitt)
    (hleft : prefixElementaryUnit E i j hij a ∈ H)
    (hright : prefixElementaryUnit E j k hjk 1 ∈ H) :
    prefixElementaryUnit E i k hik a ∈ H := by
  have hc :
      ⁅prefixElementaryUnit E i j hij a,
        prefixElementaryUnit E j k hjk 1⁆ ∈ H := by
    rw [commutatorElement_def]
    exact H.mul_mem
      (H.mul_mem (H.mul_mem hleft hright) (H.inv_mem hleft))
      (H.inv_mem hright)
  rw [prefixElementaryUnit_commutator E i j k hij hjk hik a 1] at hc
  simpa using hc
end SoficGroups.SourceGeneration
