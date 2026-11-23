-- Prove2me | solution 1 for OEdge.wellFounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:26.836683+00:00
-- url     : https://prove2.me/submissions/770a6b1a-16e3-48b5-8335-28126be1651c

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
namespace OEdge
theorem _root_.solution {n m} : @WellFounded (OBdd n m) OEdge := by
  suffices s : Subrelation (@OEdge n m) (InvImage Nat.lt OBdd.var) from Subrelation.wf s (InvImage.wf _ (Nat.lt_wfRel.wf))
  rintro ⟨x, hx⟩ ⟨y, hy⟩ ⟨h1, h2⟩
  simp_all only []
  rw [← h1] at h2
  let xs := x.toRelevantPointer
  let ys : x.RelevantPointer := ⟨y.root, Relation.ReflTransGen.tail Relation.ReflTransGen.refl h2⟩
  have h3 : RelevantEdge x xs ys := h2
  apply hx at h3
  simp only [RelevantMayPrecede, Bdd.toRelevantPointer, xs, ys] at h3
  simp only [InvImage, OBdd.var, Nat.succ_eq_add_one, Nat.lt_eq, Fin.val_fin_lt, gt_iff_lt]
  rcases hp : x.root
  case terminal => simp_all only [Ordered, MayPrecede, Nat.succ_eq_add_one, toVar_terminal_eq, var]
  case node j => rcases hq : y.root <;> simp_all
end OEdge
