-- Prove2me | solution 1 for ThreeSum.OneHotMask.eval_maskOf
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T14:40:41.035578+00:00
-- url     : https://prove2.me/submissions/df459fc2-5020-4863-a12f-a9cfab6477bb

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.List.Basic
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask

open Finset SubsetAddress LocalHashMoments
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false
























private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ range (L+1)) (hL : L ∉ s) : s ⊆ range L := by
  intro i hi
  have h := mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact mem_range.mpr (by omega)

theorem eval_maskOf_sourceProof {L : ℕ} (s : Finset ℕ) (hs : s ⊆ range L)
    (w0 w1 : ℕ → ℕ) :
    eval w0 w1 L (maskOf s) = ∑ i ∈ range L, if i ∈ s then w1 i else w0 i := by
  induction L generalizing s with
  | zero => simp [eval]
  | succ L ih =>
    by_cases hL : L ∈ s
    · have ht : s.erase L ⊆ range L :=
        subset_range_pred ((erase_subset L s).trans hs) (notMem_erase _ _)
      have he : 2^L + maskOf (s.erase L) = maskOf s :=
        add_sum_erase s (fun i => 2^i) hL
      have hlo : ¬maskOf s < 2^L := by omega
      have hsub : maskOf s-2^L = maskOf (s.erase L) := by omega
      rw [eval, if_neg hlo, hsub, ih (s.erase L) ht, sum_range_succ, if_pos hL]
      congr 1
      apply sum_congr rfl
      intro i hi
      have hiL : i ≠ L := by have := mem_range.mp hi; omega
      by_cases hiS : i ∈ s <;> simp [hiS, hiL]
    · have ht := subset_range_pred hs hL
      have hlo := (maskOf_isMask ht).1
      rw [eval, if_pos hlo, ih s ht, sum_range_succ, if_neg hL]















































end ThreeSum.OneHotMask

end


theorem solution : ∀ {L : Nat} (s : Finset.{0} Nat),
  @LE.le.{0} (Finset.{0} Nat)
      (@Preorder.toLE.{0} (Finset.{0} Nat)
        (@PartialOrder.toPreorder.{0} (Finset.{0} Nat) (@Finset.instPartialOrder.{0} Nat)))
      s (Finset.range L) →
    ∀ (w0 w1 : Nat → Nat),
      @Eq.{1} Nat (ThreeSum.OneHotMask.eval w0 w1 L (ThreeSum.SubsetAddress.maskOf s))
        (∑ i ∈ Finset.range L,
          @ite.{1} Nat
            (@Membership.mem.{0, 0} Nat (Finset.{0} Nat)
              (@SetLike.instMembership.{0, 0} (Finset.{0} Nat) Nat (@Finset.instSetLike.{0} Nat)) s i)
            (@Finset.decidableMem.{0} Nat instDecidableEqNat i s) (w1 i) (w0 i)) := by
  exact @ThreeSum.OneHotMask.eval_maskOf_sourceProof

#print axioms solution
