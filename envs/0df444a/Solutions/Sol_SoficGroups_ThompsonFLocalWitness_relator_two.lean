-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.relator_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/6aaecd2b-1031-470e-b87d-3121c555500e

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_append
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_generator_three_eq_prefixInsertion
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_generator_difference_action_one_one
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_commute_prefixInsertion_of_prefixWordAction_fixed

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    Commute (generatorA * generatorB⁻¹)
      ((generatorA ^ 2)⁻¹ * generatorB * generatorA ^ 2) := by
  rw [generator_three_eq_prefixInsertion]
  apply commute_prefixInsertion_of_prefixWordAction_fixed
    (generatorA * generatorB⁻¹) [1, 1, 1] _ generatorA
  simpa using
    prefixWordAction_append generator_difference_action_one_one [1]
end SoficGroups.ThompsonFLocalWitness
