-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.bandwise_moment_nat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:57:48.975124+00:00
-- url     : https://prove2.me/submissions/9db95702-32d3-4d9e-a8d6-43e60655f099

import Definitions.Def_SharpIntermediateSubgroupBounds_Escape
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Order
import Mathlib.Tactic.Ring
import Definitions.Def_SharpIntermediateSubgroupBounds_Packing
import Theorems.Thm_SharpIntermediateSubgroupBounds_bandwise_moment
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
import Theorems.Thm_SharpIntermediateSubgroupBounds_escapeBranchProduct_cons
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.escapeBranchProduct_cons



set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
noncomputable section
universe u
variable {G : Type u} [Group G] [Fintype G]
attribute [local instance] SharpIntermediateSubgroupBounds.packingSubgroupDecidableEq
attribute [local instance] SharpIntermediateSubgroupBounds.subgroupFinite
namespace SharpIntermediateSubgroupBounds
theorem _root_.solution {H : Subgroup G} (hn : 1 < H.index)
    {q : ℕ} (hq : 1 < q) (hqp : q ≤ H.index.minFac) (r : ℕ) :
    gammaNum q r *
        (∑ K : band H q r, H.relIndex K.1 ^ r) ≤
      gammaDen q r * H.index ^ r := by
  have hdenPos : 0 < gammaDen q r := pow_pos (by omega) _
  have h := bandwise_moment hn hq hqp r
  rw [gammaQ] at h
  have hqRat :
      (gammaNum q r : ℚ) *
          (∑ K : band H q r, H.relIndex K.1 ^ r) ≤
        (gammaDen q r : ℚ) * (H.index : ℚ) ^ r := by
    calc
      (gammaNum q r : ℚ) *
            (∑ K : band H q r, H.relIndex K.1 ^ r) =
          (gammaDen q r : ℚ) *
            ((gammaNum q r : ℚ) / gammaDen q r *
              (∑ K : band H q r,
                (H.relIndex K.1 : ℚ) ^ r)) := by
        simp only [Nat.cast_sum, Nat.cast_pow]
        field_simp
      _ ≤ (gammaDen q r : ℚ) * (H.index : ℚ) ^ r :=
        mul_le_mul_of_nonneg_left h (by positivity)
  exact_mod_cast hqRat
end SharpIntermediateSubgroupBounds
