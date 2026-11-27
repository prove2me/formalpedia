-- Prove2me | solution 1 for TreeStack.OrientedBranch.exists_root_auxCompactPotential_le_rootEstimate_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:41:23.929373+00:00
-- url     : https://prove2.me/submissions/7296cbac-f63c-40cc-b761-cce349ffad02

import Mathlib
import Definitions.Def_TreeStack_Consolidation
import Definitions.Def_TreeStack_UpperBound
import Theorems.Thm_TreeStack_OrientedBranch_auxInternalDegreePotential_le_rootedInternalPotential
import Theorems.Thm_TreeStack_OrientedBranch_exists_root_auxHeight_le_dist
import Theorems.Thm_TreeStack_OrientedBranch_rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hScores : ∀ v, score T C v ≤ 0) :
    ∃ r : V,
      auxCompactPotential C ambientRoot hScores ≤
        (rootEstimate T r : ℤ) - 1 := by
  rcases
      exists_root_auxHeight_le_dist C ambientRoot hScores with
    ⟨r, hHeight⟩
  refine ⟨r, ?_⟩
  have hInternal :=
    auxInternalDegreePotential_le_rootedInternalPotential
      C ambientRoot hScores r hHeight
  rw [rootEstimate_eq_one_add_ambientLeafCount_add_rootedInternalPotential
    T r]
  unfold auxCompactPotential
  push_cast
  linarith
end TreeStack.OrientedBranch
