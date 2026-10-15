-- Prove2me | solution 1 for ThreeSum.LightCoverKeyData.Stored.of_kept
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:19:40.558934+00:00
-- url     : https://prove2.me/submissions/60ae15ea-f2f6-460c-a7ce-845d922ec173

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.GCDMonoid.Nat
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
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
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
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.Prime.Basic
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
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
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
import Theorems.Thm_ThreeSum_LightLocalCoverTables_Data_of_kept


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace Light
end Light
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightLocalCoverLayout
end ThreeSum.LightLocalCoverLayout
namespace ThreeSum.LightLocalCoverMetadata
end ThreeSum.LightLocalCoverMetadata
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSumApsp
end ThreeSumApsp

section


/-!
# Segments of the memory

Seg μ a l says that the cells a, a + 1, …, a + l.length - 1 of the memory μ hold the list l.
SegN is Seg for a list of natural numbers, MatAt for a matrix written row by row, VecAt for a vector
of indices.  The file has the lemmas for reading a cell of a segment, writing into it, writing
elsewhere, and for cutting and joining segments.  Each of the four predicates has its lemma `keep`,
which carries it to a later memory.
-/

@[expose] public section

namespace Light

open ThreeSumApsp







variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}































































/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]

































































































































end Light

end
end

section


/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000


































































































theorem globalKeys_length (h J : ℕ) :
    (globalKeys h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  rw [globalKeys_eq_map,List.length_map,globalRecords_length]































end ThreeSum.GlobalKeyEnumeration

end

section


/-! # Retained local-cover tables survive reuse of the returned free region -/

namespace ThreeSum.LightLocalCoverRetention

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout LightLocalCoverMetadata

set_option maxHeartbeats 1000000

theorem base_le_nextFree (base h : ℕ) : base ≤ nextFree base h := by
  unfold nextFree scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total
  omega

theorem table_ends_le (base h : ℕ) :
    maps base h+rows h*(2*(512*h)) ≤ nextFree base h ∧
    hist0 base h+rows h*localPrime h ≤ nextFree base h ∧
    hist1 base h+rows h*localPrime h ≤ nextFree base h ∧
    matrixPtr base h+rows h*cols h ≤ nextFree base h ∧
    candidates base h+scheduleSize h ≤ nextFree base h := by
  unfold nextFree scheduleMaps candidates work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr
    LightCoverGreedy.total LightCoverGreedy.out
  omega

theorem data_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : Data μ h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h))
    (K : Kept μ ν (nextFree base h)) :
    Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) := by
  obtain ⟨hm,hl,hr,hx,_⟩ := table_ends_le base h
  exact H.of_kept K hm hl hr hx

theorem rows_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ScheduleRows μ h (scheduleMaps base h))
    (K : Kept μ ν (nextFree base h)) :
    ScheduleRows ν h (scheduleMaps base h) := by
  intro s hs i hi
  have hm := Nat.mul_le_mul_right (2*(512*h)) (show s+1 ≤ scheduleSize h by omega)
  simp only [Nat.add_mul,one_mul] at hm
  rw [K _ (by unfold nextFree; omega),K _ (by unfold nextFree; omega)]
  exact H s hs i hi

theorem indices_of_kept {μ ν : ℕ → ℤ} {base h : ℕ}
    (H : ∀ s : Occurrence h, μ (candidates base h+s.val) = (candidateAt h s : ℤ))
    (K : Kept μ ν (nextFree base h)) :
    ∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ) := by
  intro s
  have he := (table_ends_le base h).2.2.2.2
  rw [K _ (by have hs := s.isLt; omega)]
  exact H s

theorem header_of_kept {μ ν : ℕ → ℤ} {free h : ℕ}
    (H : Seg μ free (LightLocalCoverInit.values free h))
    (K : Kept μ ν (nextFree (LightLocalCoverInit.base free) h)) :
    Seg ν free (LightLocalCoverInit.values free h) := by
  have he : free+20 ≤ nextFree (LightLocalCoverInit.base free) h :=
    base_le_nextFree (LightLocalCoverInit.base free) h
  apply H.congr
  intro i hi
  have hi' : i < 20 := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,values] using hi
  exact K _ (by omega)




end ThreeSum.LightLocalCoverRetention

end

section


/-!
# The retained cover, output layers, and exact global key array

This bundle is produced by the actual cover/key host and remains valid when
later phases use its computed next free address. In particular the output
index decoder can read the original layer masks without reconstructing them.
-/

namespace ThreeSum.LightCoverKeyData

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000




theorem global_length (h J : ℕ) : (globalKeys h J).length=LightGlobalKeys.localCount h^J := by
  simp only [globalKeys_length,LightGlobalKeys.localCount,mul_pow]

theorem layer_end_le_header (free h J : ℕ) :
    LightCoverKeys.afterCover free h+outputCount (512*h) h ≤ LightCoverKeys.keyHeader free h J := by
  unfold LightCoverKeys.keyHeader LightGlobalKeys.scratch
  omega

theorem afterCover_le_keyEnd (free h J : ℕ) : LightCoverKeys.afterCover free h ≤ keyEnd free h J := by
  have hh := layer_end_le_header free h J
  unfold keyEnd
  omega


























theorem Stored.of_kept_sourceProof {μ ν : ℕ → ℤ} {free h J : ℕ} (H : Stored μ free h J)
    (K : Kept μ ν (keyEnd free h J)) : Stored ν free h J := by
  have hafter := afterCover_le_keyEnd free h J
  have hafterK : Kept μ ν (LightCoverKeys.afterCover free h) := fun i hi => K i (by omega)
  refine ⟨?_,?_,LightLocalCoverRetention.header_of_kept H.header hafterK,
    LightLocalCoverRetention.data_of_kept H.data hafterK,
    LightLocalCoverRetention.rows_of_kept H.rows hafterK,
    LightLocalCoverRetention.indices_of_kept H.indices hafterK,?_⟩
  · rw [K _ (by unfold keyEnd; omega)]
    exact H.count
  · apply H.keys.congr
    intro i hi
    rw [global_length] at hi
    exact K _ (by unfold keyEnd; omega)
  · intro i hi
    have hh := layer_end_le_header free h J
    rw [K _ (by unfold keyEnd; omega)]
    exact H.masks i hi










end ThreeSum.LightCoverKeyData

end


theorem solution : ∀ {μ ν : Nat → Int} {free h J : Nat},
  ThreeSum.LightCoverKeyData.Stored μ free h J →
    Light.Kept μ ν (ThreeSum.LightCoverKeyData.keyEnd free h J) → ThreeSum.LightCoverKeyData.Stored ν free h J := by
  exact @ThreeSum.LightCoverKeyData.Stored.of_kept_sourceProof

#print axioms solution
