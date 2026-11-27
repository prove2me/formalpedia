-- Prove2me | solution 1 for TreeStack.OrientedBranch.mass_le_auxDegreePotential_sub_leafSlack
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:37:29.670836+00:00
-- url     : https://prove2.me/submissions/14d437b8-8f88-4ec3-ae61-11da7af74d0e

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
import Theorems.Thm_TreeStack_OrientedBranch_auxWeightedMass_sub_configurationSlack_eq_mass
import Theorems.Thm_TreeStack_OrientedBranch_auxLeafSlack_le_auxConfigurationSlack
import Theorems.Thm_TreeStack_OrientedBranch_auxWeightedMass_le_auxDegreePotential


set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (mass C : ℤ) ≤
      auxDegreePotential C ambientRoot hScores -
        auxLeafSlack C ambientRoot hScores := by
  have hWeighted :=
    auxWeightedMass_le_auxDegreePotential
      C ambientRoot hRootPos hScores
  have hSlack :=
    auxLeafSlack_le_auxConfigurationSlack
      C ambientRoot hScores
  have hMass :=
    auxWeightedMass_sub_configurationSlack_eq_mass
      C ambientRoot hScores
  linarith
end TreeStack.OrientedBranch
