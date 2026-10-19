-- Prove2me | solution 1 for SoficGroups.SourceGeneration.ninePrefixElementaryGroup_le_sourceGenerated
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:36:51.68578+00:00
-- url     : https://prove2.me/submissions/aa2cc910-fd9f-4b19-9383-f456513bbf21

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_SourceGeneration_prefixElementaryGroup_le_of_hub
import Theorems.Thm_SoficGroups_SourceGeneration_nineRoot_to_alphaHub_mem_sourceGenerated
import Theorems.Thm_SoficGroups_SourceGeneration_nineRoot_from_alphaHub_mem_sourceGenerated

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
    prefixElementaryGroup ninePrefixCode ≤ sourceGeneratedGroup :=
  prefixElementaryGroup_le_of_hub ninePrefixCode sourceGeneratedGroup
    (0 : Fin 9) nineRoot_to_alphaHub_mem_sourceGenerated
    nineRoot_from_alphaHub_mem_sourceGenerated
end SoficGroups.SourceGeneration
