-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.source_generators_not_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/03984769-1246-4d4e-91b2-5ee7f796d2ef

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixInsertionHom_injective
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_generators_not_commute

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    ¬ Commute sourceGeneratorA sourceGeneratorB := by
  intro hcommute
  apply generators_not_commute
  apply Commute.of_map
    (prefixInsertionHom_injective ThompsonPrefixLocal.sourceLocalWord)
  apply (commute_iff_eq _ _).2
  have heq := congrArg
    (fun x :
      localPrefixTranspositionGroup ThompsonPrefixLocal.sourceLocalWord =>
      (x : BinaryLeavittˣ)) hcommute.eq
  simpa only [sourceGeneratorA, sourceGeneratorB, Subgroup.coe_mul]
    using heq
end SoficGroups.ThompsonFLocalWitness
