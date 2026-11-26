-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.relative_escape_coset_band
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:57.35983+00:00
-- url     : https://prove2.me/submissions/0742d27f-6f57-4c31-a2fc-86d4cb41adbf

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_relative_escape_coset

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
    (_hlo : H.index.minFac ^ r ≤ H.relIndex K)
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaQ H.index.minFac r * (H.relIndex K : ℚ) ^ r ≤
      (Nat.card (CosetRelGen H K r) : ℚ) :=
  relative_escape_coset hn hHK hhi
end SharpIntermediateSubgroupBounds
