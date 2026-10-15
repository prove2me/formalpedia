-- Prove2me | solution 1 for ThreeSum.ReportingHostMasks.localChildren_mem
-- status  : ACCEPTED   (prove)
-- author  : @wurtle
-- created : 2026-10-14T15:18:24.105253+00:00
-- url     : https://prove2.me/submissions/361bb28a-2e22-4905-8186-89f33b77d387

import Aesop
import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Logic
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Regions
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle09
import Definitions.Def_ThreeSum1962Source_Bundle10
import Definitions.Def_ThreeSum1962Source_Bundle11
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
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
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.Cast.Lemmas
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.Sublists
import Mathlib.Data.Nat.Cast.Order.Ring
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
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
import Theorems.Thm_ThreeSum_ReportingHostMasks_blockSet_localRow


set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option Elab.async false
namespace ThreeSum.BlockEncoding
end ThreeSum.BlockEncoding
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockMaskLayout
end ThreeSum.BlockMaskLayout
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalEncoding
end ThreeSum.GlobalEncoding
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress

section


/-!
# Flattening a block family of subsets

The coordinates retain the block index explicitly. Joining and slicing are
mutually inverse, preserve Boolean set operations, and give exact cardinalities
for balanced full inputs and forced prefixes.
-/

namespace ThreeSum.BlockRows

open Finset
open scoped BigOperators











@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma















@[simp] theorem row_join {J L : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (i : Fin J) :
    row (join I u) i = if i ∈ I then u i else ∅ := by
  ext x
  by_cases hi : i ∈ I <;> simp [hi]








































theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _








































end ThreeSum.BlockRows

end

section


/-!
# Positive-prefix reporting for concrete guarded incidences

The band triple is fixed by the input index sets and offset passed to this
module. Its wanted queries retain the original A index, signed lift and
full output tuple, including every chosen-map occurrence. Children are
the balanced subsets of the next output block, in deterministic colex order.
-/

namespace ThreeSum.RawReporting

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences








theorem mem_childList {L h : ℕ} {Q S : Finset (Fin L)} :
    S ∈ childList Q h ↔ S ∈ Q.powersetCard h := by
  constructor
  · intro hs
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    obtain ⟨s, hsLayer, rfl⟩ := Finset.mem_map.mp ((Finset.mem_sort _).mp hc)
    exact hsLayer
  · intro hs
    apply List.mem_map.mpr
    refine ⟨toColex S, ?_, rfl⟩
    apply (Finset.mem_sort _).mpr
    exact Finset.mem_map.mpr ⟨S, hs, rfl⟩














































section FixedBand

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]






















































































end FixedBand

end ThreeSum.RawReporting

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


















@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (Coord J L)) :
    (indexSet S).card = S.card := Finset.card_map _

@[simp] theorem unindex_index {J L : ℕ} (S : Finset (Coord J L)) :
    unindexSet (indexSet S) = S := by
  ext c
  simp [unindexSet,indexSet]









@[simp] theorem indexSet_subset {J L : ℕ} (S T : Finset (Coord J L)) :
    indexSet S ⊆ indexSet T ↔ S ⊆ T := by
  simp [indexSet]

















































































end ThreeSum.BlockIndex

end

section


/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks

open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced








@[simp] theorem blockSet_card {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    (blockSet i S).card = S.card := by
  simp [blockSet,join_card]





@[simp] theorem blockSet_subset {J L : ℕ} (i : Fin J) (S T : Finset (Fin L)) :
    blockSet i S ⊆ blockSet i T ↔ S ⊆ T := by
  rw [blockSet,blockSet,indexSet_subset]
  constructor
  · intro h x hx
    exact (mem_join.mp (h (x := Sigma.mk i x) (mem_join.mpr ⟨by simp,hx⟩))).2
  · intro h ⟨j,x⟩ hx
    exact mem_join.mpr ⟨(mem_join.mp hx).1,h (mem_join.mp hx).2⟩




@[simp] theorem localRow_blockSet {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    localRow i (blockSet i S) = S := by
  simp [localRow,blockSet]































theorem globalChildren_mem {J L : ℕ} (i : Fin J) (Q S : Finset (Fin L)) (h : ℕ) :
    blockSet i S ∈ globalChildren i Q h ↔ S ⊆ Q ∧ S.card = h := by
  simp [globalChildren,QueryCoordinates.missingSets_mem]

theorem localChildren_mem_sourceProof {J L : ℕ} (i : Fin J) (Q S : Finset (Fin L)) (h : ℕ) :
    S ∈ localChildren i Q h ↔ S ∈ RawReporting.childList Q h := by
  rw [RawReporting.mem_childList,Finset.mem_powersetCard]
  constructor
  · intro hs
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hs
    have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
    have he := blockSet_localRow i Q ht.1
    have hc : (localRow i T).card = T.card := by
      simpa only [blockSet_card] using congrArg Finset.card he
    exact ⟨(blockSet_subset i _ _).mp (he.symm ▸ ht.1),hc.trans ht.2⟩
  · intro hs
    exact List.mem_map.mpr ⟨blockSet i S,(globalChildren_mem i Q S h).mpr hs,localRow_blockSet i S⟩



































































































































































end ThreeSum.ReportingHostMasks

end


theorem solution : ∀ {J L : Nat} (i : Fin J) (Q S : Finset.{0} (Fin L)) (h : Nat),
  Iff
    (@Membership.mem.{0, 0} (Finset.{0} (Fin L)) (List.{0} (Finset.{0} (Fin L)))
      (@List.instMembership.{0} (Finset.{0} (Fin L))) (@ThreeSum.ReportingHostMasks.localChildren J L i Q h) S)
    (@Membership.mem.{0, 0} (Finset.{0} (Fin L)) (List.{0} (Finset.{0} (Fin L)))
      (@List.instMembership.{0} (Finset.{0} (Fin L))) (@ThreeSum.RawReporting.childList L Q h) S) := by
  exact @ThreeSum.ReportingHostMasks.localChildren_mem_sourceProof

#print axioms solution
