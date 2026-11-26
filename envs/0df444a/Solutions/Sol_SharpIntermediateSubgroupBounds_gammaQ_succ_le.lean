-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaQ_succ_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:53:23.040904+00:00
-- url     : https://prove2.me/submissions/12d7ade7-c35b-4219-ac79-b6e5804d373a

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_succ
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_nonneg

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p r : ℕ} (hp : 1 < p) :
    gammaQ p (r + 1) ≤ gammaQ p r := by
  rw [gammaQ_succ p r (by omega)]
  apply mul_le_of_le_one_right (gammaQ_nonneg hp)
  exact sub_le_self _ (by positivity)
end SharpIntermediateSubgroupBounds
