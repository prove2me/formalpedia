-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.rawRelGen_card_eq_cardH_pow_mul_cosetRelGen_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:57.361085+00:00
-- url     : https://prove2.me/submissions/c683c058-0670-47e5-837e-7cd668ec475c

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow

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
      Nat.card H ^ r * Nat.card (CosetRelGen H K r) := by
  rw [rawRelGen_card_eq_cosetRelGen_card_mul_cardH_pow hHK r,
    Nat.mul_comm]
end SharpIntermediateSubgroupBounds
