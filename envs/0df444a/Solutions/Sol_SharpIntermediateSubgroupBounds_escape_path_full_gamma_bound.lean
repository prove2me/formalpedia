-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.escape_path_full_gamma_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:54:15.800069+00:00
-- url     : https://prove2.me/submissions/a62b5c31-cfd0-4b25-840d-27d8ac415727

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_antitone
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeStrictCount_le
import Theorems.Thm_SharpIntermediateSubgroupBounds_escape_path_branchProduct_bound

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
    {s : EscapeState K} (hHs : H ≤ s.1) (z : EscapePath K r s) :
    gammaQ H.index.minFac r * (Nat.card K : ℚ) ^ r ≤
      (BranchingTree.branchProduct (EscapeChoice K) (escapeNext K) z : ℚ) := by
  apply le_trans
    (mul_le_mul_of_nonneg_right
      (gammaQ_antitone
        ((Nat.minFac_prime (by omega : H.index ≠ 1)).one_lt)
        (escapeStrictCount_le K z)) (by positivity))
  exact escape_path_branchProduct_bound hn hHK hHs z
end SharpIntermediateSubgroupBounds
