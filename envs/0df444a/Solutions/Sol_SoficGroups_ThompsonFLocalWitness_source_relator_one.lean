-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.source_relator_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/755ec270-520c-4ecb-b3e5-17c7e24238c6

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_relator_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    Commute (sourceGeneratorA * sourceGeneratorB⁻¹)
      (sourceGeneratorA⁻¹ * sourceGeneratorB * sourceGeneratorA) := by
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  simpa only [sourceGeneratorA, sourceGeneratorB,
    Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv] using
    (relator_one.map
      (prefixInsertionHom ThompsonPrefixLocal.sourceLocalWord)).eq
end SoficGroups.ThompsonFLocalWitness
