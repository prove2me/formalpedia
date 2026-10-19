-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.relator_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/9c35ac5a-4e1c-4058-84ca-df25b95aad26

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_generator_two_eq_prefixInsertion
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
      (generatorA⁻¹ * generatorB * generatorA) := by
  rw [generator_two_eq_prefixInsertion]
  exact commute_prefixInsertion_of_prefixWordAction_fixed
    (generatorA * generatorB⁻¹) [1, 1]
    generator_difference_action_one_one generatorA
end SoficGroups.ThompsonFLocalWitness
