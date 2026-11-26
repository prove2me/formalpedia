-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.gammaQ_eq_gammaProdQ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:52:01.04125+00:00
-- url     : https://prove2.me/submissions/8622eaad-cb9c-4b36-bdc1-aee90d57ee82

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
import Theorems.Thm_SharpIntermediateSubgroupBounds_gammaDen_eq_prod_pow

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupDecidableEq
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution (p r : ℕ) (hp : 0 < p) :
    gammaQ p r = gammaProdQ p r := by
  rw [gammaQ, gammaNum, gammaDen_eq_prod_pow, gammaProdQ]
  rw [Nat.cast_prod, Nat.cast_prod, ← Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  have hpow : 1 ≤ p ^ (j + 1) :=
    one_le_pow₀ (Nat.one_le_iff_ne_zero.mpr hp.ne')
  rw [Nat.cast_sub hpow, Nat.cast_one, Nat.cast_pow]
  have hne : (p : ℚ) ^ (j + 1) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr hp.ne')
  field_simp
end SharpIntermediateSubgroupBounds
