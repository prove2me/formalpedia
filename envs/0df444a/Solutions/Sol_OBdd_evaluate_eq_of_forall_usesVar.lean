-- Prove2me | solution 1 for OBdd.evaluate_eq_of_forall_usesVar
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:41.996106+00:00
-- url     : https://prove2.me/submissions/5975d37e-a90f-48fa-9bae-5cf72a13b85f

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_OBdd_usesVar_of_dependsOn
import Theorems.Thm_Nary_eq_of_forall_dependency_getElem_eq
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {O : OBdd n m} {I J : Vector Bool n} :
    (∀ i, O.1.usesVar i → I[i] = J[i]) → O.evaluate I = O.evaluate J := by
  intro h
  apply Nary.eq_of_forall_dependency_getElem_eq
  rintro ⟨i, hi⟩
  apply h
  simp only [Nary.DependsOn, Nary.IndependentOf, not_forall] at hi
  rcases hi with ⟨b, v, hbv⟩
  apply usesVar_of_dependsOn hbv
end OBdd
