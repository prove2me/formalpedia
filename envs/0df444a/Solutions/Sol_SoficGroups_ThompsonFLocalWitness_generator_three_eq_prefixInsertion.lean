-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.generator_three_eq_prefixInsertion
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/e5ded0b4-514b-4844-87be-08bdcf7a5cad

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_append
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixInsertionHom_conjugate_of_prefixWordAction
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_rootRotation_action_one
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_generator_two_eq_prefixInsertion

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    (generatorA ^ 2)⁻¹ * generatorB * generatorA ^ 2 =
      prefixInsertionHom [1, 1, 1] generatorA := by
  have hrotation :
      PrefixWordAction rootRotation [1, 1] [1, 1, 1] := by
    simpa using prefixWordAction_append rootRotation_action_one [1]
  calc
    (generatorA ^ 2)⁻¹ * generatorB * generatorA ^ 2 =
        rootRotation *
          (generatorA⁻¹ * generatorB * generatorA) *
          rootRotation⁻¹ := by
            simp [generatorA, pow_two, mul_assoc]
    _ = rootRotation * prefixInsertionHom [1, 1] generatorA *
          rootRotation⁻¹ := by rw [generator_two_eq_prefixInsertion]
    _ = prefixInsertionHom [1, 1, 1] generatorA :=
      prefixInsertionHom_conjugate_of_prefixWordAction
        rootRotation [1, 1] [1, 1, 1] hrotation generatorA
end SoficGroups.ThompsonFLocalWitness
