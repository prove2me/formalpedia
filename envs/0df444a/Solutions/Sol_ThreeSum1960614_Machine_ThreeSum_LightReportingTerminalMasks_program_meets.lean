-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:09:29.355979+00:00
-- url     : https://prove2.me/submissions/fdef4f1f-27f0-456f-8928-6387043b3f7c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
import Definitions.Def_ThreeSum1960614_Machine_Bundle024
import Definitions.Def_ThreeSum1960614_Machine_Bundle025
import Definitions.Def_ThreeSum1960614_Machine_Bundle026
import Definitions.Def_ThreeSum1960614_Machine_Bundle027
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
import Definitions.Def_ThreeSum1960614_Machine_Bundle029
import Definitions.Def_ThreeSum1960614_Machine_Bundle030
import Definitions.Def_ThreeSum1960614_Machine_Bundle031
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
import Definitions.Def_ThreeSum1962Source_Bundle12
import Definitions.Def_ThreeSum1962Source_Bundle13
import Definitions.Def_ThreeSum1962Source_Bundle14
import Lean
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
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Sigma
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.Int.SuccPred
import Mathlib.Data.List.Basic
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Sublists
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockChildren_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockForced
end ThreeSum.BlockForced
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockIndexedQuery
end ThreeSum.BlockIndexedQuery
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.LightBlockChildren
end ThreeSum.LightBlockChildren
namespace ThreeSum.LightReportingTerminalMasks
end ThreeSum.LightReportingTerminalMasks
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostMasks
end ThreeSum.ReportingHostMasks
namespace ThreeSum.ReportingHostTerminalChoices
end ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
end ThreeSum1960614.Machine.ThreeSum.LightBlockChildren
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
end ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
end ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
end ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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









@[simp] theorem mem_join {J L : ℕ} {I : Finset (Fin J)}
    {u : Fin J → Finset (Fin L)} {i : Fin J} {x : Fin L} :
    Sigma.mk i x ∈ _root_.ThreeSum.BlockRows.join I u ↔ i ∈ I ∧ x ∈ u i := Finset.mem_sigma























theorem join_disjoint_compl {J L : ℕ} (I : Finset (Fin J))
    (u v : Fin J → Finset (Fin L)) : Disjoint (_root_.ThreeSum.BlockRows.join I u) (_root_.ThreeSum.BlockRows.join Iᶜ v) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hx hy
  exact (Finset.mem_compl.mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hy).1) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx).1



theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (_root_.ThreeSum.BlockRows.join I u).card = I.card * h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]











end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference
open _root_.ThreeSum.MaskDifference


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    _root_.ThreeSum.SubsetAddress.subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [_root_.ThreeSum.SubsetAddress.subsetMask,_root_.ThreeSum.SubsetAddress.maskOf,_root_.ThreeSum.SubsetAddress.natPositions]

@[simp] theorem subsetMask_empty (L : ℕ) : _root_.ThreeSum.SubsetAddress.subsetMask (∅ : Finset (Fin L)) = 0 := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum]









end ThreeSum.MaskDifference

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Calls

Meets lim P p d vals μ T R is the specification of a procedure: procedure number p of the program P,
run at depth d on the arguments vals in the memory μ, ends within T steps with a result and a memory
that satisfy R. A routine is proved to meet such a specification (Meets.of_body), and a caller uses
the specification only, so that the proof of a caller does not depend on the body of a callee.

The specification of a routine x, as its callers assume it, has the form
`∀ (data) μ, hypotheses → ∀ d, d + k ≤ lim.depth → Meets lim P p d vals μ T R`.  Here k is the
number of levels of calls that x needs below itself, and d, the depth at which the body of x runs,
comes last.

There is one rule for calls, in four forms.  It is told the fact about the callee, from which it
reads the values of the arguments, the time and what holds afterwards, and it asks for what follows
the call.  Three side goals have default proofs: the arguments are safe and have these values, one
more level of calls is allowed, and the time suffices.  Ends.callTo and Ends.callToThen are the rule
for a state ⟨frame l, μ⟩; Ends.callLast and Ends.callThen are the same for local variables that are
not given as a list.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Specifications of procedures -/



section
variable {p : ℕ} {vals : List ℤ} {μ : ℕ → ℤ} {T T' : ℕ} {R R' : ℤ → (ℕ → ℤ) → Prop}



/-- More time and a weaker conclusion. -/
theorem Meets.mono (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T') (hR : ∀ r μ', R r μ' → R' r μ') :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R' := by
  obtain ⟨body, hp, he⟩ := h
  exact ⟨body, hp, he.mono hT fun _ => hR _ _⟩







end

/-! ## The rule for calls -/

section
variable {loc μ : ℕ → ℤ} {l : List ℤ} {T T' p x : ℕ} {args : List _root_.ThreeSum1960614.Machine.Light.Expr} {vals : List ℤ}
  {R : ℤ → (ℕ → ℤ) → Prop} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} {s : _root_.ThreeSum1960614.Machine.Light.Stmt}









end

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

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
open _root_.Light


open _root_.ThreeSumApsp
open _root_.ThreeSum1960614.Machine.ThreeSumApsp





variable {μ μ' μ'' : ℕ → ℤ} {a b n : ℕ} {l l₁ l₂ : List ℤ} {x : ℤ}





















































/-- Reading a cell of a segment of natural numbers, with the proof that the index is in range. -/
theorem SegN.getElem {l : List ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SegN μ a l) {i : ℕ} (hi : i < l.length) :
    μ (a + i) = (l[i] : ℕ) := by
  rw [h i (by simpa using hi), List.getElem_map]

























end Light

end

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











@[simp] theorem indexSet_card {J L : ℕ} (S : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    (_root_.ThreeSum.BlockIndex.indexSet S).card = S.card := Finset.card_map _



@[simp] theorem index_unindex {J L : ℕ} (S : Finset (Fin (J*L))) :
    _root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockIndex.unindexSet (J := J) (L := L) S) = S := by
  ext c
  simp [_root_.ThreeSum.BlockIndex.unindexSet,_root_.ThreeSum.BlockIndex.indexSet]





@[simp] theorem indexSet_union {J L : ℕ} (S T : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    _root_.ThreeSum.BlockIndex.indexSet (S∪T) = _root_.ThreeSum.BlockIndex.indexSet S ∪ _root_.ThreeSum.BlockIndex.indexSet T := by
  exact Finset.map_union S T













end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates
open _root_.ThreeSum.QueryCoordinates


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators















@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (_root_.ThreeSum.QueryCoordinates.positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W),_root_.ThreeSum.QueryCoordinates.positions_toFinset,_root_.ThreeSum.SubsetAddress.natPositions_card]



















@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).length = xs.length.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.setLayer,List.length_sublistsLen]























@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).length = Q.card.choose k := by
  simp [_root_.ThreeSum.QueryCoordinates.missingSets]



end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockIndexedQuery


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open scoped _root_.BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

@[simp] theorem prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (_root_.ThreeSum.BlockRows.prefixIndices J k).card = k := by
  simpa only [_root_.ThreeSum.BlockRows.prefixIndices,Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := J) (m := k))













theorem leftPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u) (_root_.ThreeSum.BlockIndexedQuery.querySet k Q) := by
  exact (Finset.disjoint_map _).mpr (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl (_root_.ThreeSum.BlockRows.prefixIndices J k) u Q)

theorem rightPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u) (_root_.ThreeSum.BlockIndexedQuery.querySet k Q) := by
  exact (Finset.disjoint_map _).mpr
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl (_root_.ThreeSum.BlockRows.prefixIndices J k) (fun i => Q i \ u i) Q)







theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (_root_.ThreeSum.BlockIndexedQuery.querySet k Q).card = (J-k)*(2*h) := by
  rw [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]







section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]



















end Histograms

end ThreeSum.BlockIndexedQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren
open _root_.ThreeSum.LightBlockChildren


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum.ReportingHostMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostMasks

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

















theorem program_meets {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.program 0 d
      [W,h,_root_.ThreeSum.SubsetAddress.subsetMask Q,_root_.ThreeSum.SubsetAddress.subsetMask A,_root_.ThreeSum.SubsetAddress.subsetMask B,_root_.ThreeSum.SubsetAddress.subsetMask R,masks,dstL,dstR,work]
      μ (_root_.ThreeSum.LightBlockChildren.time W Q.card h)
      (fun r μ' =>
        r = (_root_.ThreeSum.SubsetAddress.subsetMask (R \ Q) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' masks ((_root_.ThreeSum.QueryCoordinates.missingSets Q h).map _root_.ThreeSum.SubsetAddress.subsetMask) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstL (_root_.ThreeSum.LightBlockChildren.leftMasks A Q h) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' dstR (_root_.ThreeSum.LightBlockChildren.rightMasks B Q h) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ μ' masks) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.meets rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.procs A B Q R hw hAQ hBQ hQR hh hmasks hleft hright hspace hword hd



end ThreeSum.LightBlockChildren

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Finite terminal completions in the actual mask enumerator's order

At any valid reporting prefix, a full balanced endpoint needs exactly
`(J-k)*h` of the remaining query coordinates. Enumerating that one layer
contains every retained completion and costs no more than the terminal
Boolean-cube allowance. The selected bucket pair masses sum to at most the
unchanged original raw prefix count.
-/

namespace ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.ReportingHostTerminalChoices


open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open scoped _root_.BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000



theorem choices_length {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hk : k≤J) :
    (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length = ((J-k)*(2*h)).choose ((J-k)*h) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices,List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_length]
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (fun i => _root_.ThreeSum.LayerCounts.mem_vertices.mp (q i).2.property)]















variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]





end ThreeSum.ReportingHostTerminalChoices

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum.LightReportingTerminalMasks


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000











theorem choiceAt_eq_get {h J k i : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (hi : i<(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt q k i=(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k)[i] := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt,List.getElem?_eq_getElem hi,Option.getD_some]



section

private theorem private_ac4ca2346f_leftMasks_eq {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) :
    _root_.ThreeSum.LightBlockChildren.leftMasks (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows pre)) (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)) ((J-k)*h)=
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).map (fun S => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockForced.prefixLeft (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪ S))) := by
  simp only [_root_.ThreeSum.LightBlockChildren.leftMasks,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices,List.map_map]
  apply List.map_congr_left
  intro S _
  simp only [Function.comp_apply,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_union,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.index_unindex,_root_.ThreeSum.BlockIndexedQuery.leftPrefix]
end


section

private theorem private_c5ca14d9e3_rightMasks_eq {h J k : ℕ} (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (464*h)))) :
    _root_.ThreeSum.LightBlockChildren.rightMasks (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre))
      (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)) ((J-k)*h)=
      (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).map (fun S => _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet
        (_root_.ThreeSum.BlockForced.prefixRight (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows pre) ∪
          (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ S)))) := by
  simp only [_root_.ThreeSum.LightBlockChildren.rightMasks,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices,List.map_map,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_union]
  apply List.map_congr_left
  intro S _
  congr 2
  change _root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ S=_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockForced.remaining (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) \ _root_.ThreeSum.BlockIndex.unindexSet S)
  simp only [_root_.ThreeSum.BlockIndex.indexSet,Finset.map_sdiff]
  rw [show (_root_.ThreeSum.BlockIndex.unindexSet S).map (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)).toEmbedding=S from _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.index_unindex S]
  rfl
end


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}





end ThreeSum.LightReportingTerminalMasks

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingTerminalMasks
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
open _root_.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
set_option maxHeartbeats 1600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.program_meets__implementation_87d748a8a9 {μ : ℕ→ℤ} {h J k masks dstL dstR work : ℕ}
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (pre : List (Finset (Fin (464*h)))) (hk : k≤J)
    (hw : (lim.space : ℤ)≤lim.word)
    (hmasks : masks+_root_.ThreeSum.LightReportingTerminalMasks.count h J k≤dstL) (hleft : dstL+_root_.ThreeSum.LightReportingTerminalMasks.count h J k≤dstR)
    (hright : dstR+_root_.ThreeSum.LightReportingTerminalMasks.count h J k≤work) (hspace : work+(2*(J*(464*h))+2)≤lim.space)
    (hword : ((2^(J*(464*h)+1) : ℕ) : ℤ)≤lim.word) (hd : d+J*(464*h)+3≤lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.program 0 d
      [((J*(464*h) : ℕ) : ℤ),(((J-k)*h : ℕ) : ℤ),_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)),masks,dstL,dstR,work]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.time h J k) (fun r ν => r=0 ∧
        (∀ i<_root_.ThreeSum.LightReportingTerminalMasks.count h J k, ν (dstL+i)=(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt q k pre i)) : ℤ)) ∧
        (∀ i<_root_.ThreeSum.LightReportingTerminalMasks.count h J k, ν (dstR+i)=(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt q k pre i)) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν masks) := by
  have hQ := _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (fun i => _root_.ThreeSum.LayerCounts.mem_vertices.mp (q i).2.property)
  have hhalf : (J-k)*h ≤ (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)).card+1 := by rw [hQ]; nlinarith
  have hrun := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockChildren.program_meets (μ := μ) (h := (J-k)*h)
    (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)) (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows q)) hw
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_disjoint_query _ _ _) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightPrefix_disjoint_query _ _ _) (Finset.Subset.refl _)
    hhalf (by simpa only [hQ,_root_.ThreeSum.LightReportingTerminalMasks.count] using hmasks) (by simpa only [hQ,_root_.ThreeSum.LightReportingTerminalMasks.count] using hleft)
    (by simpa only [hQ,_root_.ThreeSum.LightReportingTerminalMasks.count] using hright) hspace hword hd
  rw [hQ] at hrun
  apply hrun.mono le_rfl
  rintro r ν ⟨hr,_,hL,hR,hkeep⟩
  refine ⟨by simpa using hr,?_,?_,hkeep⟩
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.private_ac4ca2346f_leftMasks_eq] at hL
    intro i hi
    have hi' : i<(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length := by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices_length q hk,_root_.ThreeSum.LightReportingTerminalMasks.count] using hi
    have hh := hL.getElem (i := i) (by simpa only [List.length_map] using hi')
    simpa only [List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.leftAt,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt_eq_get q hi'] using hh
  · rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.private_c5ca14d9e3_rightMasks_eq] at hR
    intro i hi
    have hi' : i<(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices q k).length := by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostTerminalChoices.choices_length q hk,_root_.ThreeSum.LightReportingTerminalMasks.count] using hi
    have hh := hR.getElem (i := i) (by simpa only [List.length_map] using hi')
    simpa only [List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.rightAt,_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.choiceAt_eq_get q hi'] using hh
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.program_meets__implementation_87d748a8a9) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingTerminalMasks.program_meets__implementation_87d748a8a9)

#print axioms solution
