-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.relative_escape_coset_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T06:02:41.026798+00:00
-- url     : https://prove2.me/submissions/1adc55a8-68a3-42e7-a5fe-0d673e5fa01e

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
    (hhi : H.relIndex K < H.index.minFac ^ (r + 1)) :
    gammaNum H.index.minFac r * H.relIndex K ^ r ≤
      gammaDen H.index.minFac r * Nat.card (CosetRelGen H K r) := by
  have hdenPos : 0 < gammaDen H.index.minFac r := by
    exact pow_pos (Nat.minFac_pos _) _
  have h := relative_escape_coset hn hHK hhi
  rw [gammaQ] at h
  have hq :
      (gammaNum H.index.minFac r : ℚ) * (H.relIndex K : ℚ) ^ r ≤
        (gammaDen H.index.minFac r : ℚ) *
          (Nat.card (CosetRelGen H K r) : ℚ) := by
    calc
      (gammaNum H.index.minFac r : ℚ) * (H.relIndex K : ℚ) ^ r =
          (gammaDen H.index.minFac r : ℚ) *
            ((gammaNum H.index.minFac r : ℚ) /
              gammaDen H.index.minFac r * (H.relIndex K : ℚ) ^ r) := by
        field_simp
      _ ≤ (gammaDen H.index.minFac r : ℚ) *
          (Nat.card (CosetRelGen H K r) : ℚ) :=
        mul_le_mul_of_nonneg_left h (by positivity)
  exact_mod_cast hq
end SharpIntermediateSubgroupBounds
