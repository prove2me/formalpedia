-- Prove2me | solution 1 for TreeStack.OrientedBranch.mass_le_auxCompactPotential
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T23:39:12.865231+00:00
-- url     : https://prove2.me/submissions/e239c9e4-f75f-4499-99ad-4d176f9a0232

import Mathlib
import Definitions.Def_TreeStack_GlobalCharge
import Definitions.Def_TreeStack_LeafSlack
import Theorems.Thm_TreeStack_OrientedBranch_mass_le_auxDegreePotential_sub_leafSlack
import Theorems.Thm_TreeStack_OrientedBranch_auxDegreePotential_sub_leafSlack_eq_auxCompactPotential

set_option autoImplicit false
open TreeStack
open scoped BigOperators Classical
open TreeStack.OrientedBranch
variable {V : Type*} [Fintype V] {T : FiniteTree V}
namespace TreeStack.OrientedBranch
theorem _root_.solution [Nontrivial V]
    (C : Configuration V) (ambientRoot : V)
    (hRootPos : 0 < C ambientRoot)
    (hScores : ∀ v, score T C v ≤ 0) :
    (mass C : ℤ) ≤
      auxCompactPotential C ambientRoot hScores := by
  rw [← auxDegreePotential_sub_leafSlack_eq_auxCompactPotential
    C ambientRoot hScores]
  exact
    mass_le_auxDegreePotential_sub_leafSlack
      C ambientRoot hRootPos hScores
end TreeStack.OrientedBranch
