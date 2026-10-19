-- Prove2me | solution 1 for SoficGroups.ThompsonFLocalWitness.generators_not_commute
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:01.668904+00:00
-- url     : https://prove2.me/submissions/61dd9624-57e6-41b9-b785-516be9d4bd9a

import Mathlib
import Definitions.Def_NonSoficGroup
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_append
import Theorems.Thm_SoficGroups_ThompsonPrefixInsertion_prefixWordAction_mul
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_prefixWordAction_inv
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_prefixWordAction_prefixInsertion
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_rootRotation_action_zero_zero
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_rootRotation_action_zero_one
import Theorems.Thm_SoficGroups_ThompsonFLocalWitness_rootRotation_action_one

set_option autoImplicit true
noncomputable section
open SoficGroups
open SoficGroups.ThompsonFLocalWitness
open ThompsonPrefixInsertion
namespace SoficGroups.ThompsonFLocalWitness
theorem _root_.solution : ¬ Commute generatorA generatorB := by
  have ha_zero_one :
      PrefixWordAction generatorA [1, 0] [0, 1] :=
    prefixWordAction_inv rootRotation_action_zero_one
  have ha_one :
      PrefixWordAction generatorA [1, 1] [1] :=
    prefixWordAction_inv rootRotation_action_one
  have hb_one_one_zero :
      PrefixWordAction generatorB [1, 1, 0] [1, 0, 1] := by
    change
      PrefixWordAction rightRotation⁻¹ [1, 1, 0] [1, 0, 1]
    apply prefixWordAction_inv
    unfold rightRotation
    simpa using
      prefixWordAction_prefixInsertion [1]
        rootRotation_action_zero_one
  have hb_one_zero :
      PrefixWordAction generatorB [1, 0] [1, 0, 0] := by
    change PrefixWordAction rightRotation⁻¹ [1, 0] [1, 0, 0]
    apply prefixWordAction_inv
    unfold rightRotation
    simpa using
      prefixWordAction_prefixInsertion [1]
        rootRotation_action_zero_zero
  have hab :
      PrefixWordAction (generatorA * generatorB)
        [1, 1, 0] [0, 1, 1] :=
    prefixWordAction_mul
      (by simpa using prefixWordAction_append ha_zero_one [1])
      hb_one_one_zero
  have hba :
      PrefixWordAction (generatorB * generatorA)
        [1, 1, 0] [1, 0, 0] :=
    prefixWordAction_mul hb_one_zero
      (by simpa using prefixWordAction_append ha_one [0])
  intro hcommute
  have hwords :
      leavittWordS [0, 1, 1] = leavittWordS [1, 0, 0] := by
    calc
      leavittWordS [0, 1, 1] =
          (↑(generatorA * generatorB) : BinaryLeavitt) *
            leavittWordS [1, 1, 0] := hab.prefixing.symm
      _ = (↑(generatorB * generatorA) : BinaryLeavitt) *
            leavittWordS [1, 1, 0] := by rw [hcommute.eq]
      _ = leavittWordS [1, 0, 0] := hba.prefixing
  apply (one_ne_zero : (1 : BinaryLeavitt) ≠ 0)
  calc
    (1 : BinaryLeavitt) =
        leavittWordT [0, 1, 1] * leavittWordS [0, 1, 1] :=
      (leavittWordT_mul_wordS_self [0, 1, 1]).symm
    _ = leavittWordT [0, 1, 1] * leavittWordS [1, 0, 0] := by
      rw [hwords]
    _ = 0 := leavittWordT_mul_wordS_of_incomparable
      [0, 1, 1] [1, 0, 0] (by decide) (by decide)
end SoficGroups.ThompsonFLocalWitness
