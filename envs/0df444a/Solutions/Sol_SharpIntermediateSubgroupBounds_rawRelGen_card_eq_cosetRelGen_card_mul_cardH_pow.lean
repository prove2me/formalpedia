-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:44:09.072424+00:00
-- url     : https://prove2.me/submissions/4fafb973-82ac-4fca-b56e-56edcdfe6ca1

import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.Coset.Card
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Escape

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution
    {H K : Subgroup G} (hHK : H ≤ K) (r : ℕ) :
    Nat.card (RawRelGen H K r) =
      Nat.card (CosetRelGen H K r) * Nat.card H ^ r := by
  calc
    Nat.card (RawRelGen H K r) =
        Nat.card (CosetRelGen H K r × (Fin r → H)) :=
      Nat.card_congr (rawRelGenEquivCosetRelGenProd hHK)
    _ = Nat.card (CosetRelGen H K r) * Nat.card (Fin r → H) :=
      Nat.card_prod _ _
    _ = Nat.card (CosetRelGen H K r) * Nat.card H ^ r := by
      rw [Nat.card_fun, Nat.card_fin]
end SharpIntermediateSubgroupBounds
