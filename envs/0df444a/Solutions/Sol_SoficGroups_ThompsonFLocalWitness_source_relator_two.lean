-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.source_relator_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/b1bf0b71-06fc-4cdf-ba6c-dcdce124cfcd

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_relator_two

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    Commute (sourceGeneratorA * sourceGeneratorB⁻¹)
      ((sourceGeneratorA ^ 2)⁻¹ * sourceGeneratorB *
        sourceGeneratorA ^ 2) := by
  apply (commute_iff_eq _ _).2
  apply Subtype.ext
  simpa only [sourceGeneratorA, sourceGeneratorB,
    Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
    map_mul, map_inv, map_pow] using
    (relator_two.map
      (prefixInsertionHom ThompsonPrefixLocal.sourceLocalWord)).eq
end SoficGroups.ThompsonFLocalWitness
