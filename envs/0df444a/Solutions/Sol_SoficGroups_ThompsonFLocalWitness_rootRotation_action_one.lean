-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.rootRotation_action_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/600cb58f-011b-41e0-84c6-49704125bf62

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
    PrefixWordAction rootRotation [1] [1, 1] := by
  unfold rootRotation
  rw [mul_assoc]
  refine prefixWordAction_mul (b := [1, 1]) ?_ ?_
  · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
      (by decide) (by decide) (by decide)
  · refine prefixWordAction_mul (b := [0]) ?_ ?_
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)
    · exact ThompsonFiniteGeneration.cylinderSwap_prefixWordAction_of_cases
        (by decide) (by decide) (by decide)
end SoficGroups.ThompsonFLocalWitness
