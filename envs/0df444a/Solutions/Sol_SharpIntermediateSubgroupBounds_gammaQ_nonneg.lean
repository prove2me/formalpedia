-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaQ_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:39.398398+00:00
-- url     : https://prove2.me/submissions/93133cee-fe1e-41c4-8b09-f02f56a2cff0

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaQ_eq_gammaProdQ

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {p r : ℕ} (hp : 1 < p) : 0 ≤ gammaQ p r := by
  rw [gammaQ_eq_gammaProdQ p r (by omega)]
  apply Finset.prod_nonneg
  intro j hj
  apply sub_nonneg.mpr
  apply (div_le_one₀ (by positivity : (0 : ℚ) < (p : ℚ) ^ (j + 1))).2
  exact_mod_cast one_le_pow₀ hp.le
end SharpIntermediateSubgroupBounds
