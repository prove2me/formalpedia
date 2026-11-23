-- Prove2me | solution 1 for OBdd.reduced_of_relevant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:05:04.79259+00:00
-- url     : https://prove2.me/submissions/ed8e14f2-67fa-4744-a115-c38b8bf40e2a

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_init_inductionOn
import Theorems.Thm_Bdd_eq_terminal_of_relevant
import Theorems.Thm_OBdd_reduced_of_terminal
import Theorems.Thm_Bdd_reduced_of_terminal
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} (S : O.1.RelevantPointer):
    O.Reduced → OBdd.Reduced ⟨{heap := O.1.heap, root := S.1}, ordered_of_relevant O S⟩ := by
  intro R
  induction O using OBdd.init_inductionOn
  case base b =>
    apply OBdd.reduced_of_terminal
    simp only [isTerminal, Ordered]
    use b
    apply eq_terminal_of_relevant rfl
  case step j _ _ _ _ o =>
    constructor
    · intro p; apply R.1 ⟨p.1, Relation.ReflTransGen.trans S.2 p.2⟩
    · intro q p _
      have : SimilarRP ⟨{ heap := O.1.heap, root := node j }, o⟩
              ⟨q.1, Relation.ReflTransGen.trans S.2 q.2⟩
              ⟨p.1, Relation.ReflTransGen.trans S.2 p.2⟩ := by
        simp_all only [SimilarRP, Similar]
      apply R.2 this
end OBdd
