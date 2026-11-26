-- Prove2me | solution 1 for SharpIntermediateSubgroupBounds.BranchingTree.leaf_product_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:50:56.156067+00:00
-- url     : https://prove2.me/submissions/61329570-08e1-40a3-882d-7eafc2b4191e

import Definitions.Def_SharpIntermediateSubgroupBounds_Basic
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Field.Rat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Rat
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Fintype.BigOperators
import Definitions.Def_SharpIntermediateSubgroupBounds_Tree
import Theorems.Thm_SharpIntermediateSubgroupBounds_BranchingTree_branchProduct_zero
attribute [local simp] SharpIntermediateSubgroupBounds.BranchingTree.branchProduct_zero

set_option autoImplicit true
open SharpIntermediateSubgroupBounds
open scoped BigOperators
open SharpIntermediateSubgroupBounds.BranchingTree
universe u
variable {State : Type*}
variable (Choice : State → Type*) [∀ s, Fintype (Choice s)]
variable (next : ∀ s, Choice s → State)
namespace SharpIntermediateSubgroupBounds.BranchingTree
theorem _root_.solution [∀ s, Nonempty (Choice s)]
    (r : ℕ) (s : State) (q : ℚ)
    (hq : ∀ z : Path Choice next r s,
      q ≤ (branchProduct Choice next z : ℚ)) :
    q ≤ (Fintype.card (Path Choice next r s) : ℚ) := by
  induction r generalizing s q with
  | zero =>
      have h := hq PUnit.unit
      simpa [Path, branchProduct] using h
  | succ r ih =>
      let b : ℕ := Fintype.card (Choice s)
      have hbNat : 0 < b := Fintype.card_pos
      have hb : (0 : ℚ) < (b : ℚ) := (Nat.cast_pos (α := ℚ)).2 hbNat
      have hchild : ∀ x : Choice s,
          q / (b : ℚ) ≤
            (Fintype.card (Path Choice next r (next s x)) : ℚ) := by
        intro x
        apply ih (s := next s x) (q := q / (b : ℚ))
        intro z
        apply (div_le_iff₀ hb).2
        let zx : Path Choice next (r + 1) s := by
          change Σ x : Choice s, Path Choice next r (next s x)
          exact ⟨x, z⟩
        have hz := hq zx
        change q ≤ ((Fintype.card (Choice s) *
          branchProduct Choice next z : ℕ) : ℚ) at hz
        simpa only [Nat.cast_mul, b, mul_comm] using hz
      calc
        q = ∑ _x : Choice s, q / (b : ℚ) := by
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [show Fintype.card (Choice s) = b by rfl]
          exact (mul_div_cancel₀ q hb.ne').symm
        _ ≤ ∑ x : Choice s,
            (Fintype.card (Path Choice next r (next s x)) : ℚ) :=
          Finset.sum_le_sum fun x _hx => hchild x
        _ = (Fintype.card (Path Choice next (r + 1) s) : ℚ) := by
          simp only [Path, Fintype.card_sigma, Nat.cast_sum]
end SharpIntermediateSubgroupBounds.BranchingTree
