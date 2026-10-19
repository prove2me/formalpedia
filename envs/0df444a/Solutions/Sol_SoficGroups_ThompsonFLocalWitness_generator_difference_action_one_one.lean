-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.generator_difference_action_one_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/509c2067-0083-4230-9a6b-e17a42ee433b

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_append
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_mul
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_prefixWordAction_inv
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_prefixWordAction_prefixInsertion
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_rootRotation_action_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    PrefixWordAction (generatorA * generatorB⁻¹) [1, 1] [1, 1] := by
  have hrotation :
      PrefixWordAction rootRotation [1, 1] [1, 1, 1] := by
    simpa using prefixWordAction_append rootRotation_action_one [1]
  have hright :
      PrefixWordAction rightRotation [1, 1] [1, 1, 1] := by
    unfold rightRotation
    simpa using
      prefixWordAction_prefixInsertion [1] rootRotation_action_one
  change
    PrefixWordAction
      (rootRotation⁻¹ * (rightRotation⁻¹)⁻¹) [1, 1] [1, 1]
  simp only [inv_inv]
  exact prefixWordAction_mul (prefixWordAction_inv hrotation) hright
end SoficGroups.ThompsonFLocalWitness
