-- Prove2me | solution 1 for SoficGroups.SourceGeneration.alphaRoot_mem_sourceGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/8c4462ba-f87c-4f8e-8c2b-9af1897b65ce

import Mathlib
import Definitions.Def_NonSoficGroup

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
    (i j : Fin 3) (hij : i ≠ j) (a : BinaryLeavitt) :
    prefixElementaryUnit alphaPrefixCode i j hij a ∈ sourceGeneratedGroup := by
  apply Subgroup.subset_closure
  apply Set.mem_union_left
  exact Subgroup.subset_closure ⟨i, j, hij, a, rfl⟩
end SoficGroups.SourceGeneration
