-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.generator_two_eq_prefixInsertion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/36fc5aa6-48e7-47b7-a3fd-c7d57eeef9f1

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixInsertionHom_conjugate_of_prefixWordAction
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_rootRotation_action_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    generatorA⁻¹ * generatorB * generatorA =
      prefixInsertionHom [1, 1] generatorA := by
  calc
    generatorA⁻¹ * generatorB * generatorA =
        rootRotation * prefixInsertionHom [1] generatorA *
          rootRotation⁻¹ := by
            rw [generatorB_eq_prefixInsertion]
            simp [generatorA]
    _ = prefixInsertionHom [1, 1] generatorA :=
      prefixInsertionHom_conjugate_of_prefixWordAction
        rootRotation [1] [1, 1] rootRotation_action_one generatorA
end SoficGroups.ThompsonFLocalWitness
