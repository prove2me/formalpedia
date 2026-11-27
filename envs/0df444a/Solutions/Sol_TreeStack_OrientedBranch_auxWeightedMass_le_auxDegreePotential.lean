-- Prove2me | solution 1 for TreeStack.OrientedBranch.auxWeightedMass_le_auxDegreePotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:35:50.426983+00:00
-- url     : https://prove2.me/submissions/b12d52db-65f9-4e5a-ad1c-e9cf38dc5550

import Mathlib
import Definitions.Def_TreeStack_AuxiliaryCharge
import Definitions.Def_TreeStack_GlobalCharge
import Theorems.Thm_TreeStack_OrientedBranch_auxWeightedMass_eq_edges_sub_defect
import Theorems.Thm_TreeStack_OrientedBranch_sum_auxEdgeContribution_le_degree_add_defect

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
set_option maxHeartbeats 800000
set_option maxHeartbeats 200000
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    auxWeightedMass C ambientRoot hScores ≤
      auxDegreePotential C ambientRoot hScores := by
  rw [auxWeightedMass_eq_edges_sub_defect]
  have h :=
    sum_auxEdgeContribution_le_degree_add_defect
      C ambientRoot hRootPos hScores
  linarith
end TreeStack.OrientedBranch
