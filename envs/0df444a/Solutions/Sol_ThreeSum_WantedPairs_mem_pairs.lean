-- Prove2me | solution 1 for ThreeSum.WantedPairs.mem_pairs
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:42:12.538665+00:00
-- url     : https://prove2.me/submissions/eab6a74e-37b9-4914-aa13-3d3dee49490c

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
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
import Mathlib.Algebra.Order.Field.Basic
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
import Mathlib.Data.Int.Cast.Lemmas
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
import Mathlib.Data.Nat.Cast.Order.Ring
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
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
import Mathlib.Tactic.Tauto
import Theorems.Thm_ThreeSum_SourceBuckets_Stored_mem_bucketList


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.LightHistogram
end ThreeSum.LightHistogram
namespace ThreeSum.SourceBuckets
end ThreeSum.SourceBuckets

section


/-!
# Exact positions of original indices in retained residue buckets

Counting-sort positions preserve every input incidence. The resulting fiber
segments contain no repeated physical indices even when input values agree.
All inverse-enumeration reasoning is semantic; the actual scatter program
writes these positions using a cursor and never searches an input band.
-/

namespace ThreeSum.SourceBuckets

open Finset LightHistogram

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000






theorem offset_succ (key : ℕ → ℕ) (N r : ℕ) :
    offset key N (r+1) = offset key N r+count key r N := by
  exact Finset.sum_range_succ _ _
































































































































































end ThreeSum.SourceBuckets

end

section


/-! # Header-driven exact views of the retained original-index buckets -/

namespace ThreeSum.SourceBucketView

open SourceBuckets LightHistogram







theorem start_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r ≤ M) :
    start μ offsets r = offset key N r := by
  simp only [start,H.offsets r hr,Int.toNat_natCast]

theorem stop_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    stop μ offsets r = offset key N (r+1) := by
  unfold stop
  rw [Nat.add_assoc,H.offsets (r+1) (by omega),Int.toNat_natCast]

theorem length_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    length μ offsets r = count key r N := by
  rw [length,start_eq H (Nat.le_of_lt hr),stop_eq H hr,offset_succ]
  omega

theorem indices_eq {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r : ℕ}
    (H : Stored μ key N M offsets flat) (hr : r < M) :
    indices μ offsets flat r = bucketList μ flat (offset key N r) (count key r N) := by
  rw [indices,start_eq H (Nat.le_of_lt hr),length_eq H hr]






theorem mem_indices {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i < M) (hr : r < M) :
    i ∈ indices μ offsets flat r ↔ i < N ∧ key i = r := by
  rw [indices_eq H hr]
  exact H.mem_bucketList hkey hr






















end ThreeSum.SourceBucketView

end

section


/-!
# Exact output-sensitive residue join semantics

The join visits a stored right-index fiber once for each left input
position. Its output is the literal list of matching position pairs.
The count is the guarded wanted mass when the left codes include the
selected common shift and the right codes are the original output keys.
-/

namespace ThreeSum.WantedPairs

open Light SourceBuckets
open scoped BigOperators

set_option maxHeartbeats 1200000














































theorem mem_pairs_sourceProof {μ : ℕ → ℤ} {offsets flat NR NL M i j : ℕ} {left right : ℕ → ℕ}
    (H : Stored μ right NR M offsets flat) (hl : ∀ a < NL, left a < M)
    (hr : ∀ b < NR, right b < M) :
    (i,j) ∈ pairs μ offsets flat left NL ↔ i < NL ∧ j < NR ∧ right j=left i := by
  constructor
  · intro hh
    obtain ⟨a,ha,hb⟩ := List.mem_flatMap.mp hh
    have ha' : a < NL := List.mem_range.mp ha
    obtain ⟨b,hb,he⟩ := List.mem_map.mp hb
    have hai : a=i := congrArg Prod.fst he
    have hbj : b=j := congrArg Prod.snd he
    subst a
    subst b
    exact ⟨ha',(SourceBucketView.mem_indices H hr (hl i ha')).mp hb⟩
  · rintro ⟨hi,hj,hkey⟩
    apply List.mem_flatMap.mpr
    refine ⟨i,List.mem_range.mpr hi,?_⟩
    apply List.mem_map.mpr
    exact ⟨j,(SourceBucketView.mem_indices H hr (hl i hi)).mpr ⟨hj,hkey⟩,rfl⟩


































































































end ThreeSum.WantedPairs

end


theorem solution : ∀ {μ : Nat → Int} {offsets flat NR NL M i j : Nat} {left right : Nat → Nat},
  ThreeSum.SourceBuckets.Stored μ right NR M offsets flat →
    (∀ (a : Nat), @LT.lt.{0} Nat instLTNat a NL → @LT.lt.{0} Nat instLTNat (left a) M) →
      (∀ (b : Nat), @LT.lt.{0} Nat instLTNat b NR → @LT.lt.{0} Nat instLTNat (right b) M) →
        Iff
          (@Membership.mem.{0, 0} (Prod.{0, 0} Nat Nat) (List.{0} (Prod.{0, 0} Nat Nat))
            (@List.instMembership.{0} (Prod.{0, 0} Nat Nat)) (ThreeSum.WantedPairs.pairs μ offsets flat left NL)
            (@Prod.mk.{0, 0} Nat Nat i j))
          (And (@LT.lt.{0} Nat instLTNat i NL) (And (@LT.lt.{0} Nat instLTNat j NR) (@Eq.{1} Nat (right j) (left i)))) := by
  exact @ThreeSum.WantedPairs.mem_pairs_sourceProof

#print axioms solution
