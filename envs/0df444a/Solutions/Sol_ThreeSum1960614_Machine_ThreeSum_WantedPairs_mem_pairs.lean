-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.WantedPairs.mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:12:12.85298+00:00
-- url     : https://prove2.me/submissions/8802389a-4a81-4ad2-88b7-97b925bee648

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_APSPSource_ThreeSumApsp_Util_Index
import Definitions.Def_APSPSource_ThreeSumApsp_Util_List
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle005
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1960614_Machine_Bundle013
import Definitions.Def_ThreeSum1960614_Machine_Bundle014
import Definitions.Def_ThreeSum1960614_Machine_Bundle015
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Group.Equiv.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Algebra.Order.Ring.Pow
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Ring.Nat
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Size
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Nat.SuccPred
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_SourceBuckets_Stored_mem_bucketList

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBucketView
end ThreeSum.SourceBucketView
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets
namespace ThreeSum.WantedPairs
end ThreeSum.WantedPairs
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightHistogram
end ThreeSum1960614.Machine.ThreeSum.LightHistogram
namespace ThreeSum1960614.Machine.ThreeSum.SourceBucketView
end ThreeSum1960614.Machine.ThreeSum.SourceBucketView
namespace ThreeSum1960614.Machine.ThreeSum.SourceBuckets
end ThreeSum1960614.Machine.ThreeSum.SourceBuckets
namespace ThreeSum1960614.Machine.ThreeSum.WantedPairs
end ThreeSum1960614.Machine.ThreeSum.WantedPairs

namespace ThreeSum1960614.Machine

/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets
open _root_.ThreeSum.SourceBuckets


open _root_.Finset
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000





theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    _root_.ThreeSum.SourceBuckets.offset key N (r+1) = _root_.ThreeSum.SourceBuckets.offset key N r+_root_.ThreeSum.LightHistogram.count key r N := by
  exact Finset.sum_range_succ _ _











































end ThreeSum.SourceBuckets

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Header-driven exact views of the retained original-index buckets -/

namespace ThreeSum.SourceBucketView
open _root_.ThreeSum.SourceBucketView


open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open _root_.ThreeSum.LightHistogram
open _root_.ThreeSum1960614.Machine.ThreeSum.LightHistogram






theorem start_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r ≤ M) :
    _root_.ThreeSum.SourceBucketView.start μ offsets r = _root_.ThreeSum.SourceBuckets.offset key N r := by
  simp only [_root_.ThreeSum.SourceBucketView.start,H.offsets r hr,Int.toNat_natCast]

theorem stop_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.stop μ offsets r = _root_.ThreeSum.SourceBuckets.offset key N (r+1) := by
  unfold _root_.ThreeSum.SourceBucketView.stop
  rw [Nat.add_assoc,H.offsets (r+1) (by omega),Int.toNat_natCast]

theorem length_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.length μ offsets r = _root_.ThreeSum.LightHistogram.count key r N := by
  rw [_root_.ThreeSum.SourceBucketView.length,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.start_eq H (Nat.le_of_lt hr),_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.stop_eq H hr,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.offset_succ]
  omega

theorem indices_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hr : r < M) :
    _root_.ThreeSum.SourceBucketView.indices μ offsets flat r = _root_.ThreeSum.SourceBuckets.bucketList μ flat (_root_.ThreeSum.SourceBuckets.offset key N r) (_root_.ThreeSum.LightHistogram.count key r N) := by
  rw [_root_.ThreeSum.SourceBucketView.indices,_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.start_eq H (Nat.le_of_lt hr),_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.length_eq H hr]



theorem mem_indices {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ _root_.ThreeSum.SourceBucketView.indices μ offsets flat r ↔ i < N ∧ key i = r := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.indices_eq H hr]
  exact H.mem_bucketList hkey hr







end ThreeSum.SourceBucketView

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.WantedPairs
open _root_.ThreeSum1960614.Machine.ThreeSum.WantedPairs

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SourceBuckets
open _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets
open scoped _root_.BigOperators
set_option maxHeartbeats 1200000
section

theorem ThreeSum1960614.Machine.ThreeSum.WantedPairs.mem_pairs__implementation_8c38d7541b {μ : ℕ → ℤ} {offsets flat NR NL M i j : ℕ} {left right : ℕ → ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.SourceBuckets.Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) :
    (i,j) ∈ _root_.ThreeSum.WantedPairs.pairs μ offsets flat left NL ↔ i < NL ∧ j < NR ∧ right j=left i := by
  constructor
  · intro hh
    obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hh
    have ha' : a < NL := List.mem_range.mp ha
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hb
    have hai : a=i := congrArg Prod.fst he
    have hbj : b=j := congrArg Prod.snd he
    subst a
    subst b
    exact ⟨ha',(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.mem_indices H hr (hl i ha')).mp hb⟩
  · rintro ⟨hi,hj,hkey⟩
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_range.mpr hi,?_⟩
    apply List.mem_map.mpr
    exact ⟨j,(_root_.ThreeSum1960614.Machine.ThreeSum.SourceBucketView.mem_indices H hr (hl i hi)).mpr ⟨hj,hkey⟩,rfl⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.WantedPairs.mem_pairs__implementation_8c38d7541b) := (@ThreeSum1960614.Machine.ThreeSum.WantedPairs.mem_pairs__implementation_8c38d7541b)

#print axioms solution
