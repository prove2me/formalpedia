-- Prove2me | solution 1 for SoficGroups.SourceGeneration.sourceGeneratedGroup_le_nine_of_compressions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/79e0ae5a-ae49-40f6-9b46-ff2d81a48dff

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
    (hu : compressionU ∈ prefixElementaryGroup ninePrefixCode)
    (hv : compressionV ∈ prefixElementaryGroup ninePrefixCode) :
    sourceGeneratedGroup ≤ prefixElementaryGroup ninePrefixCode := by
  rw [sourceGeneratedGroup, Subgroup.closure_le]
  intro z hz
  rcases hz with hz | hz
  · exact alphaPrefixElementaryGroup_le_nine hz
  · simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl
    · exact hu
    · exact hv
end SoficGroups.SourceGeneration
