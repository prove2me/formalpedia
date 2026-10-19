-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.rootRotation_action_zero_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/495262ef-c9d4-4619-b53a-a5fcf5ac40ee

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_mul
import Theorems.Thm_SoficGroups_ThompsonFiniteGeneration_cylinderSwap_prefixWordAction_of_cases

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution :
    PrefixWordAction rootRotation [0, 1] [1, 0] := by
  unfold rootRotation
  rw [mul_assoc]
  refine prefixWordAction_mul (b := [0]) ?_ ?_
  · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
      (by decide) (by decide) (by decide)
  · refine prefixWordAction_mul (b := [1, 1]) ?_ ?_
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)
end SoficGroups.ThompsonFLocalWitness
