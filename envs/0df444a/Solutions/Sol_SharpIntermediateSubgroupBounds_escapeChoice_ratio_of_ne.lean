-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escapeChoice_ratio_of_ne
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:51:45.596467+00:00
-- url     : https://prove2.me/submissions/15cecd8f-1fd3-4ecf-8196-3061dbbb09d5

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_card_mul_relIndex
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeChoice_card_add

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (K : Subgroup G) (s : EscapeState K)
    (hs : s.1 ≠ K) :
    (Fintype.card (EscapeChoice K s) : ℚ) / Nat.card K =
      1 - 1 / (s.1.relIndex K : ℚ) := by
  let c := Fintype.card (EscapeChoice K s)
  let a := Nat.card s.1
  let k := Nat.card K
  let t := s.1.relIndex K
  have hsumNat : c + a = k := escapeChoice_card_add K s hs
  have hprodNat : a * t = k := card_mul_relIndex s.2
  have haPos : 0 < a := Nat.card_pos
  have htPos : 0 < t := by
    letI : s.1.IsFiniteRelIndex K := s.1.isFiniteRelIndex_of_finiteIndex
    exact Nat.pos_of_ne_zero Subgroup.relIndex_ne_zero
  have hkPos : 0 < k := Nat.card_pos
  have hsum : (c : ℚ) + a = k := by exact_mod_cast hsumNat
  have hprod : (a : ℚ) * t = k := by exact_mod_cast hprodNat
  have hc : (c : ℚ) = k - a := eq_sub_of_add_eq hsum
  change (c : ℚ) / k = 1 - 1 / (t : ℚ)
  rw [hc, ← hprod]
  have ha : (a : ℚ) ≠ 0 := (Nat.cast_pos.mpr haPos).ne'
  have ht : (t : ℚ) ≠ 0 := (Nat.cast_pos.mpr htPos).ne'
  field_simp
end SharpIntermediateSubgroupBounds
