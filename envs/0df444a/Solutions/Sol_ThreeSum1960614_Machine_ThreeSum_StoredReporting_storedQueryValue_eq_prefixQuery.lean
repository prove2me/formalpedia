-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:22:00.931753+00:00
-- url     : https://prove2.me/submissions/a2984656-652b-426e-938e-2ab118fecc7a

import Aesop
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockForced_transformPrefixValue_eq_bucket_sum
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_RawPrefixCounts_prefixQuery_eq_bucketPrefixMass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_StoredReporting_positivePrefix_valid

namespace Finset
end Finset
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting

namespace ThreeSum1960614.Machine

/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows
open _root_.ThreeSum.BlockRows


open _root_.Finset
open scoped _root_.BigOperators















































@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting
open _root_.ThreeSum.StoredReporting


set_option maxRecDepth 8000

open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced

section

private theorem private_4ccb502193_ofFn_take_eq_iff {α : Type*} {J k : ℕ} (f g : Fin J → α) :
    (List.ofFn f).take k = (List.ofFn g).take k ↔ ∀ i : Fin J, i.val < k → f i = g i := by
  constructor
  · intro he i hi
    have hh := congrArg (fun xs => xs[i.val]?) he
    simpa only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos i.isLt,
      Option.some.injEq] using hh
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]
      by_cases hiJ : i < J
      · simp only [List.getElem?_ofFn, dif_pos hiJ, h ⟨i, hiJ⟩ hi]
      · simp only [List.getElem?_ofFn, dif_neg hiJ]
    · simp only [List.getElem?_take, hi, ite_false]
end






theorem take_prefixRows {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k ≤ J) : (List.ofFn (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)).take k = pre := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k
  · have hiJ : i < J := hi.trans_le hk
    have hip : i < pre.length := hp ▸ hi
    simp only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos hiJ, _root_.ThreeSum.StoredReporting.prefixRows,
      List.getElem?_eq_getElem hip, Option.getD_some]
  · rw [List.getElem?_take_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (by omega)]

theorem completions_eq_completedTuples {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (u : Fin J → Finset (Fin (464 * h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions q k ((List.ofFn u).take k) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples q (_root_.ThreeSum.BlockRows.prefixIndices J k) u := by
  ext t
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.completions, _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.completedTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.partitionWord, _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.private_4ccb502193_ofFn_take_eq_iff, _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices]





section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]























end Indices

end ThreeSum.StoredReporting

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting

set_option maxRecDepth 8000
open _root_.Finset
open scoped _root_.BigOperators
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery__implementation_e36a94037b {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464 * h)))) (hk : k ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue P d A B C a b c w k pre =
      (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue
  split
  next hp =>
    have hpre := _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.take_prefixRows (J := J) pre hp.1 hk
    have he := _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue_eq_bucket_sum P d B C b c w.2.2
      (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) (fun i hi => hp.2 i (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi))
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.prefixQuery_eq_bucketPrefixMass, _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts.bucketPrefixMass]
    by_cases hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
        (a w.1 % P + _root_.ThreeSum.RawIncidences.lift w.2.1 * P + d) - _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2
    · simp only [hkey, ite_true]
      rw [← _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.completions_eq_completedTuples, hpre] at he
      exact he
    · simp only [hkey, ite_false, Nat.cast_zero]
  next hp =>
    have hz : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre = 0 := by
      by_contra hn
      exact hp (_root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.positivePrefix_valid _ w pre hk (Nat.pos_of_ne_zero hn))
    simp only [hz, Nat.cast_zero]
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery__implementation_e36a94037b.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery__implementation_e36a94037b.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
