-- Prove2me | solution 1 for OBdd.not_reduced_of_sim_high_low
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T06:58:03.194807+00:00
-- url     : https://prove2.me/submissions/6a4d90c9-80a3-43ac-bb1d-35a4ff644fd9

import Mathlib.Data.Fintype.Sum
import Init.Data.ToString.Basic
import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Fintype.Vector
import Mathlib.Tactic.Linarith
import Definitions.Def_Bdd_Nary
import Definitions.Def_Bdd_DecisionTree
import Definitions.Def_Bdd_Basic
import Theorems.Thm_Nary_restrict_const
attribute [local simp] Nary.restrict_const



set_option autoImplicit true
open Pointer
open Bdd
attribute [local instance_reducible] OBdd Bdd.Ordered
namespace OBdd
theorem _root_.solution {n m} {O : OBdd n m} {j : Fin m} (h : O.1.root = node j) :
    Similar (O.high h) (O.low h) → ¬ O.Reduced := by
  intro iso R
  apply R.1 O.1.toRelevantPointer
  simp [toRelevantPointer]
  rw [h]
  constructor
  have giso : SimilarRP O ⟨(O.high h).1.root, reachable_of_edge (edge_of_high (h := h) O.1)⟩
                                ⟨(O.low  h).1.root, reachable_of_edge (edge_of_low  (h := h) O.1)⟩ := iso
  exact (symm (R.2 giso))
end OBdd
