-- Prove2me | solution 1 for ThreeSum.BlockIndex.maskHash_left
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:09:55.726096+00:00
-- url     : https://prove2.me/submissions/6ea18f6c-0ddd-4573-a5d6-b53400d87430

import Aesop
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
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
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Abel
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
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

























































@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    extend f i.val = f i := by simp [extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ natPositions s ↔ i ∈ s := by
  simp only [natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    eval (extend w0) (extend w1) L (subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [subsetMask, eval_maskOf _ (natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [extend_fin, mem_natPositions]























end ThreeSum.OneHotMask

end

section


/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex

open Finset BlockRows BlockEncoding GlobalEncoding LocalHashMoments LocalCoverBounds
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false














@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (Coord J L)) (c : Coord J L) :
    coordEquiv J L c ∈ indexSet S ↔ c ∈ S := by
  simp [indexSet]

























theorem eval_indexSet {J L : ℕ} (S : Finset (Coord J L))
    (w0 w1 : Coord J L → ℕ) :
    OneHotMask.eval (OneHotMask.extend (w0 ∘ (coordEquiv J L).symm))
      (OneHotMask.extend (w1 ∘ (coordEquiv J L).symm))
      (J*L) (SubsetAddress.subsetMask (indexSet S)) =
      ∑ c : Coord J L, if c ∈ S then w1 c else w0 c := by
  rw [OneHotMask.eval_subsetMask]
  rw [← (coordEquiv J L).sum_comp
    (fun i => if i ∈ indexSet S then (w1 ∘ (coordEquiv J L).symm) i
      else (w0 ∘ (coordEquiv J L).symm) i)]
  apply sum_congr rfl
  intro c _
  simp only [Function.comp_apply, Equiv.symm_apply_apply, mem_indexSet]

theorem positionalHash_ofFn (p : ℤ) {J : ℕ} (f : Fin J → ℤ) :
    Radix.positionalHash p id (List.ofFn f) = ∑ i : Fin J, p^i.val * f i := by
  induction J with
  | zero => simp [Radix.positionalHash]
  | succ J ih =>
    simp only [List.ofFn_succ,Radix.positionalHash, id_eq,ih,
      Fin.sum_univ_succ,Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring












theorem maskHash_left_sourceProof {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) :
    (maskHash o false S : ℤ) = endpointLeft o S := by
  unfold maskHash
  rw [eval_indexSet]
  unfold endpointLeft
  rw [positionalHash_ofFn]
  push_cast
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  unfold rawHash
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : Sigma.mk i x ∈ S
  · simp [coefficient,LocalGraph.leftWord,mem_row,hx]
  · simp [coefficient,LocalGraph.leftWord,mem_row,hx]




















end ThreeSum.BlockIndex

end


theorem solution : ∀ {h J : Nat} (o : ThreeSum.BlockEncoding.Occurrences h J)
  (S :
    Finset.{0}
      (ThreeSum.BlockRows.Coord J
        (@HMul.hMul.{0, 0, 0} Nat Nat Nat (@instHMul.{0} Nat instMulNat)
          (@OfNat.ofNat.{0} Nat (nat_lit 512) (instOfNatNat (nat_lit 512))) h))),
  @Eq.{1} Int (@Nat.cast.{0} Int instNatCastInt (@ThreeSum.BlockIndex.maskHash h J o Bool.false S))
    (@ThreeSum.BlockEncoding.endpointLeft h J o S) := by
  exact @ThreeSum.BlockIndex.maskHash_left_sourceProof

#print axioms solution
