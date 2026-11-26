-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.relative_escape_raw
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:55:31.561535+00:00
-- url     : https://prove2.me/submissions/42fc23d7-6356-4446-8286-1722a68524e3

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapePath_card_lower_bound
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapePathToRawRelGen_injective

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H K : Subgroup G}
    (hn : 1 < H.index) (hHK : H ≤ K) {r : ℕ}
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaQ H.index.minFac r * (Nat.card K : ℚ) ^ r ≤
      (Nat.card (RawRelGen H K r) : ℚ) := by
  letI : Finite (RawRelGen H K r) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  letI : Fintype (RawRelGen H K r) := Fintype.ofFinite _
  have hpaths := escapePath_card_lower_bound hn hHK r
  have hcard : Fintype.card (EscapePath K r ⟨H, hHK⟩) ≤
      Fintype.card (RawRelGen H K r) :=
    Fintype.card_le_of_injective (escapePathToRawRelGen hHK hhi)
      (escapePathToRawRelGen_injective hHK hhi)
  apply hpaths.trans
  rw [Nat.card_eq_fintype_card]
  exact_mod_cast hcard
end SharpIntermediateSubgroupBounds
