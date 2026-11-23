-- Prove2me | solution 1 for OBdd.card_RelevantPointer_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:16.2028+00:00
-- url     : https://prove2.me/submissions/fa068434-52ab-467e-83af-9417487ba0d4

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
theorem _root_.solution {O : OBdd n m} : Fintype.card O.1.RelevantPointer ≤ m + 2 := by
  conv =>
    rhs
    rw [← Fintype.card_fin m]
    rw [← Fintype.card_bool]
  rw [← Fintype.card_sum]
  let emb : O.1.RelevantPointer → Fin m ⊕ Bool := fun
    | ⟨terminal b, _⟩ => .inr b
    | ⟨node j, _⟩ => .inl j
  refine Fintype.card_le_of_embedding ⟨emb, ?_⟩
  rintro ⟨x, hx⟩ ⟨y, hy⟩ h
  cases x with
  | terminal b =>
    cases y with
    | node j => simp [emb] at h
    | terminal c => simp [emb] at h; simp_rw [h]
  | node j =>
    cases y with
    | node i => simp [emb] at h; simp_rw [h]
    | terminal b => simp [emb] at h
end OBdd
