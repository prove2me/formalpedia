-- Prove2me | solution 1 for SoficGroups.SourceGeneration.compressionV_mem_sourceGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/9a721cf3-28c7-405b-af5e-f9c6ed10c40b

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
theorem _root_.solution :
    compressionV ∈ sourceGeneratedGroup := by
  apply Subgroup.subset_closure
  apply Set.mem_union_right
  simp
end SoficGroups.SourceGeneration
