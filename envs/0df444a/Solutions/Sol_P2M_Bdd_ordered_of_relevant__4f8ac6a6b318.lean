-- Prove2me | solution 1 for P2M_Bdd_ordered_of_relevant__4f8ac6a6b318
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:09:29.388422+00:00
-- url     : https://prove2.me/submissions/a940fb87-2fce-4fcf-8a03-54cd71857eef

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
namespace Bdd
theorem _root_.solution {B : Bdd n m} {h : B.heap = v} {r : B.root = q} :
    B.Ordered → Reachable v q p → Bdd.Ordered {heap := v, root := p} := by
  intro o r_q_p
  simp_all only [Ordered]
  rintro ⟨x, hx⟩ ⟨y, hy⟩ e
  simp_all only [RelevantEdge, RelevantMayPrecede, MayPrecede, Nat.succ_eq_add_one]
  simp at hx
  simp at hy
  have : RelevantEdge B ⟨x, (by trans p <;> aesop)⟩
                        ⟨y, (by trans p <;> aesop)⟩ := by
    simp only [RelevantEdge]
    rw [h]
    assumption
  apply o at this
  rw [← h]
  exact this
end Bdd
