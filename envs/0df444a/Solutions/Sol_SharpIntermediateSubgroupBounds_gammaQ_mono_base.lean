-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaQ_mono_base
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:44.636986+00:00
-- url     : https://prove2.me/submissions/74427e4f-b56f-47c9-8a26-0ae0804a2239

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
theorem _root_.solution {q p r : ℕ} (hq : 1 < q) (hqp : q ≤ p) :
    gammaQ q r ≤ gammaQ p r := by
  rw [gammaQ_eq_gammaProdQ q r (by omega),
    gammaQ_eq_gammaProdQ p r (lt_of_lt_of_le (by omega) hqp)]
  apply Finset.prod_le_prod
  · intro j hj
    apply sub_nonneg.mpr
    apply (div_le_one₀ (by positivity :
      (0 : ℚ) < (q : ℚ) ^ (j + 1))).2
    exact one_le_pow₀ (by exact_mod_cast hq.le : (1 : ℚ) ≤ q)
  · intro j hj
    have hpow : (q : ℚ) ^ (j + 1) ≤ (p : ℚ) ^ (j + 1) :=
      pow_le_pow_left₀ (by positivity) (by exact_mod_cast hqp) _
    have hinv := one_div_le_one_div_of_le
      (by positivity : (0 : ℚ) < (q : ℚ) ^ (j + 1)) hpow
    exact sub_le_sub_left hinv 1
end SharpIntermediateSubgroupBounds
