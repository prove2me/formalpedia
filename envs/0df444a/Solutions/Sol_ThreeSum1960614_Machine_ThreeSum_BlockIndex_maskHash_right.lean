-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash_right
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:13:51.92144+00:00
-- url     : https://prove2.me/submissions/59d5b495-47eb-4c31-9e76-03a3ec45081c

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Lean
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

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Evaluating a one-hot hash from a subset mask

The executable recursion examines exactly one bit per level using a cached
power of two.  Its result is the sum of the selected symbol coefficients,
and is connected here to the raw hashes used by the global encoding.
-/

namespace ThreeSum.OneHotMask
open _root_.ThreeSum.OneHotMask


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false











@[simp] theorem extend_fin {L : ℕ} (f : Fin L → ℕ) (i : Fin L) :
    _root_.ThreeSum.OneHotMask.extend f i.val = f i := by simp [_root_.ThreeSum.OneHotMask.extend, i.isLt]

@[simp] theorem mem_natPositions {L : ℕ} (s : Finset (Fin L)) (i : Fin L) :
    i.val ∈ _root_.ThreeSum.SubsetAddress.natPositions s ↔ i ∈ s := by
  simp only [_root_.ThreeSum.SubsetAddress.natPositions, mem_map]
  constructor
  · rintro ⟨a,ha,he⟩
    have hai : a = i := Fin.ext he
    simpa only [hai] using ha
  · intro hi
    exact ⟨i,hi,rfl⟩

theorem eval_subsetMask {L : ℕ} (s : Finset (Fin L)) (w0 w1 : Fin L → ℕ) :
    _root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend w0) (_root_.ThreeSum.OneHotMask.extend w1) L (_root_.ThreeSum.SubsetAddress.subsetMask s) =
      ∑ i : Fin L, if i ∈ s then w1 i else w0 i := by
  rw [_root_.ThreeSum.SubsetAddress.subsetMask, _root_.ThreeSum.OneHotMask.eval_maskOf _ (_root_.ThreeSum.SubsetAddress.natPositions_subset s), Finset.sum_range]
  apply sum_congr rfl
  intro i _
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin, _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.mem_natPositions]





end ThreeSum.OneHotMask

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Explicit row-major encoding of the block ground set

Block coordinates are numbered by `block * width + coordinate`. The
equivalence connects compact machine-mask tables on `Fin (J*L)` with the
sigma-typed block sets in the reporting proof. Flattened one-hot coefficients
already include their positional radix factors.
-/

namespace ThreeSum.BlockIndex
open _root_.ThreeSum.BlockIndex


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false









@[simp] theorem mem_indexSet {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) (c : _root_.ThreeSum.BlockRows.Coord J L) :
    _root_.ThreeSum.BlockIndex.coordEquiv J L c ∈ _root_.ThreeSum.BlockIndex.indexSet S ↔ c ∈ S := by
  simp [_root_.ThreeSum.BlockIndex.indexSet]













theorem eval_indexSet {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L))
    (w0 w1 : _root_.ThreeSum.BlockRows.Coord J L → ℕ) :
    _root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend (w0 ∘ (_root_.ThreeSum.BlockIndex.coordEquiv J L).symm))
      (_root_.ThreeSum.OneHotMask.extend (w1 ∘ (_root_.ThreeSum.BlockIndex.coordEquiv J L).symm))
      (J*L) (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet S)) =
      ∑ c : _root_.ThreeSum.BlockRows.Coord J L, if c ∈ S then w1 c else w0 c := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_subsetMask]
  rw [← (_root_.ThreeSum.BlockIndex.coordEquiv J L).sum_comp
    (fun i => if i ∈ _root_.ThreeSum.BlockIndex.indexSet S then (w1 ∘ (_root_.ThreeSum.BlockIndex.coordEquiv J L).symm) i
      else (w0 ∘ (_root_.ThreeSum.BlockIndex.coordEquiv J L).symm) i)]
  apply sum_congr rfl
  intro c _
  simp only [Function.comp_apply, Equiv.symm_apply_apply, _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.mem_indexSet]

theorem positionalHash_ofFn (p : ℤ) {J : ℕ} (f : Fin J → ℤ) :
    _root_.ThreeSum.Radix.positionalHash p id (List.ofFn f) = ∑ i : Fin J, p^i.val * f i := by
  induction J with
  | zero => simp [_root_.ThreeSum.Radix.positionalHash]
  | succ J ih =>
    simp only [List.ofFn_succ,_root_.ThreeSum.Radix.positionalHash, id_eq,ih,
      Fin.sum_univ_succ,Fin.val_zero,pow_zero,one_mul,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring









end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex

open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open scoped _root_.BigOperators
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
section

theorem ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash_right__implementation_fd9bc5b2de {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J)
    (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash o true S : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight o S := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.eval_indexSet]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.positionalHash_ofFn]
  push_cast
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro i _
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawHash
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro x _
  by_cases hx : Sigma.mk i x ∈ S
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coefficient,_root_.ThreeSum.LocalGraph.rightWord,_root_.ThreeSum.BlockRows.mem_row,hx]
  · simp [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.coefficient,_root_.ThreeSum.LocalGraph.rightWord,_root_.ThreeSum.BlockRows.mem_row,hx]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash_right__implementation_fd9bc5b2de) := (@ThreeSum1960614.Machine.ThreeSum.BlockIndex.maskHash_right__implementation_fd9bc5b2de)

#print axioms solution
