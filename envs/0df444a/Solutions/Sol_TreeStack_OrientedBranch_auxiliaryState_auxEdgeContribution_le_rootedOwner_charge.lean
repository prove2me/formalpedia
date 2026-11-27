-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxiliaryState_auxEdgeContribution_le_rootedOwner_charge
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:25:42.838234+00:00
-- url     : https://prove2.me/submissions/cdaccffb-5783-43ec-b8fe-8dca8c616c42

import Mathlib
import Definitions.Def_TreeStack_Auxiliary
import Definitions.Def_TreeStack_AuxiliaryCharge
import Theorems.Thm_TreeStack_OrientedBranch_defectArrow_auxEdgeContribution_le_tail_charge
import Theorems.Thm_TreeStack_OrientedBranch_defectArrow_auxEdgeContribution_le_head_charge
import Theorems.Thm_TreeStack_OrientedBranch_twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
import Theorems.Thm_TreeStack_OrientedBranch_rootedOwner_eq_root_or_parent


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0)
    (B : OrientedBranch T)
    (hState :
      (B.DefectiveSupportEdge C ∧ B.DefectArrow C) ∨
        B.TwoNegativeOwnerArrow C ambientRoot) :
    auxEdgeContribution C ambientRoot hScores B ≤
      auxWeightInt C ambientRoot hScores B.root +
        auxWeightInt C ambientRoot hScores B.parent +
        auxWeightInt C ambientRoot hScores (B.rootedOwner ambientRoot) *
          scoreDefect T C (B.rootedOwner ambientRoot) := by
  rcases hState with hOriented | hTwo
  · rcases B.rootedOwner_eq_root_or_parent ambientRoot with
      hOwnerRoot | hOwnerParent
    · have h :=
        defectArrow_auxEdgeContribution_le_tail_charge
          C ambientRoot hScores B hOriented.1 hOriented.2
      rw [hOwnerRoot]
      exact h
    · have h :=
        defectArrow_auxEdgeContribution_le_head_charge
          C ambientRoot hScores B hOriented.1 hOriented.2
      rw [hOwnerParent]
      exact h
  · have h :=
      twoNegativeOwnerArrow_auxEdgeContribution_le_owner_charge
        C ambientRoot hScores B hTwo
    rw [← hTwo.2.2.2]
    exact h
end TreeStack.OrientedBranch
