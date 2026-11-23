-- Prove2me | solution 1 for OBdd.usesVar_iff_dependsOn_of_reduced
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:43.201601+00:00
-- url     : https://prove2.me/submissions/b81c67ad-28bf-4792-a8fd-b4ca558913b6

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_dependsOn_of_usesVar_of_reduced
import Theorems.Thm_OBdd_usesVar_of_dependsOn
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} :
    O.Reduced → (O.1.usesVar i ↔ Nary.DependsOn O.evaluate i) := by
  intro hr
  constructor
  · rintro ⟨j, hj, hi⟩
    simp only [Nary.DependsOn, Nary.IndependentOf, not_forall]
    use true
    apply OBdd.dependsOn_of_usesVar_of_reduced hr hj hi
  · intro nind
    simp only [Nary.DependsOn, Nary.IndependentOf, not_forall] at nind
    rcases nind with ⟨b, v, hbv⟩
    exact usesVar_of_dependsOn hbv
end OBdd
