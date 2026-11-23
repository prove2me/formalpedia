-- Prove2me | solution 1 for Pointer.toVar_lt_of_trans_edge_of_ordered
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T07:10:51.704279+00:00
-- url     : https://prove2.me/submissions/256e1653-cfd5-4086-aa42-7c5870c61fb9

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
namespace Pointer
theorem _root_.solution :
    Bdd.Ordered ⟨M, x⟩ → Relation.TransGen (Edge M) x y → x.toVar M < y.toVar M := by
  intro h1 h2
  induction h2 with
  | single e =>
    have := h1 (relevantEdge_of_edge_of_reachable e .refl)
    simp_all
  | tail r e t =>
    have := h1 (relevantEdge_of_edge_of_reachable e (Relation.TransGen.to_reflTransGen r))
    simp_all only [Nat.succ_eq_add_one, RelevantMayPrecede, MayPrecede, gt_iff_lt]
    omega
end Pointer
