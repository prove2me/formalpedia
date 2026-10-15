-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:50:10.396979+00:00
-- url     : https://prove2.me/submissions/faba1566-f944-4428-94f2-af7b1bf3d173

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
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
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
import Mathlib.Data.List.Sublists
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixQueryHost_program_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_StoredReporting_storedQueryValue_eq_prefixQuery
import Theorems.Thm_ThreeSum_BlockIndexedQuery_index_suffixDomain

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
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixQueryIndexed
end ThreeSum.LightReportingSuffixQueryIndexed
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.SubsetStages
end ThreeSum.SubsetStages
namespace ThreeSum.SubsetTransport
end ThreeSum.SubsetTransport
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
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.SubsetStages
end ThreeSum1960614.Machine.ThreeSum.SubsetStages
namespace ThreeSum1960614.Machine.ThreeSum.SubsetTransport
end ThreeSum1960614.Machine.ThreeSum.SubsetTransport

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

theorem join_subset {J L : ℕ} (I : Finset (Fin J)) {u v : Fin J → Finset (Fin L)}
    (h : ∀ i ∈ I, u i ⊆ v i) : _root_.ThreeSum.BlockRows.join I u ⊆ _root_.ThreeSum.BlockRows.join I v := by
  intro ⟨i, x⟩ hx
  obtain ⟨hi, hx⟩ := _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mp hx
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_join.mpr ⟨hi, h i hi hx⟩

theorem join_card {J L : ℕ} (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) :
    (_root_.ThreeSum.BlockRows.join I u).card = ∑ i ∈ I, (u i).card := Finset.card_sigma _ _

theorem join_card_of_balance {J L h : ℕ} (I : Finset (Fin J))
    (u : Fin J → Finset (Fin L)) (hu : ∀ i ∈ I, (u i).card = h) :
    (_root_.ThreeSum.BlockRows.join I u).card = I.card * h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card]
  simp only [Finset.sum_congr rfl hu, Finset.sum_const, Nat.nsmul_eq_mul]







@[simp] theorem mem_prefixIndices {J k : ℕ} {i : Fin J} :
    i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k ↔ i.val < k := by simp [_root_.ThreeSum.BlockRows.prefixIndices]



end ThreeSum.BlockRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Canonical suffix stages of a compact zeta table

Stage `j` has processed exactly the last `j` coordinates. Advancing one
stage is one ordinary zeta pass. Every value and every predecessor used
by these stages remains inside the same cardinality downset.
-/

namespace ThreeSum.SubsetStages
open _root_.ThreeSum.SubsetStages


open _root_.Finset



@[simp] theorem mem_suffix {L j : ℕ} (a : Fin L) : a ∈ _root_.ThreeSum.SubsetStages.suffix L j ↔ L-j ≤ a.val := by
  simp [_root_.ThreeSum.SubsetStages.suffix]























end ThreeSum.SubsetStages

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Transporting compact subset transforms across an explicit equivalence -/

namespace ThreeSum.SubsetTransport
open _root_.ThreeSum.SubsetTransport


open _root_.Finset
open scoped _root_.BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]



@[simp] theorem reindex_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    _root_.ThreeSum.SubsetTransport.reindex e f (S.map e.toEmbedding) = f S := by
  unfold _root_.ThreeSum.SubsetTransport.reindex
  congr 1
  ext a
  simp

theorem sum_powerset_map (e : α ≃ β) (S : Finset α) (f : Finset β → ℤ) :
    (∑ T ∈ (S.map e.toEmbedding).powerset, f T) =
      ∑ T ∈ S.powerset, f (T.map e.toEmbedding) := by
  simp only [Finset.map_eq_image]
  rw [Finset.powerset_image,Finset.sum_image]
  intro A hA B hB he
  exact (Finset.image_inj e.injective).mp he





theorem partialZeta_map (e : α ≃ β) (f : Finset α → ℤ) (processed S : Finset α) :
    _root_.ThreeSum.Subset.partialZeta (processed.map e.toEmbedding) (_root_.ThreeSum.SubsetTransport.reindex e f) (S.map e.toEmbedding) =
      _root_.ThreeSum.Subset.partialZeta processed f S := by
  unfold _root_.ThreeSum.Subset.partialZeta
  rw [← Finset.map_inter,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.sum_powerset_map]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.map_sdiff,← Finset.map_union,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.reindex_map]

theorem mobius_partial_product_map (e : α ≃ β) (f g : Finset α → ℤ)
    (processed preL preR Q : Finset α) :
    _root_.ThreeSum.Subset.mobius (fun S =>
      _root_.ThreeSum.Subset.partialZeta (processed.map e.toEmbedding) (_root_.ThreeSum.SubsetTransport.reindex e f) (preL.map e.toEmbedding ∪ S) *
      _root_.ThreeSum.Subset.partialZeta (processed.map e.toEmbedding) (_root_.ThreeSum.SubsetTransport.reindex e g) (preR.map e.toEmbedding ∪ S))
      (Q.map e.toEmbedding) =
      _root_.ThreeSum.Subset.mobius (fun S => _root_.ThreeSum.Subset.partialZeta processed f (preL ∪ S) *
        _root_.ThreeSum.Subset.partialZeta processed g (preR ∪ S)) Q := by
  unfold _root_.ThreeSum.Subset.mobius
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.sum_powerset_map]
  simp only [← Finset.map_union,_root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.partialZeta_map,Finset.card_map]

end ThreeSum.SubsetTransport

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







@[simp] theorem indexSet_subset {J L : ℕ} (S T : Finset (_root_.ThreeSum.BlockRows.Coord J L)) :
    _root_.ThreeSum.BlockIndex.indexSet S ⊆ _root_.ThreeSum.BlockIndex.indexSet T ↔ S ⊆ T := by
  simp [_root_.ThreeSum.BlockIndex.indexSet]















end ThreeSum.BlockIndex

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



theorem suffixStage_le (J L k : ℕ) : _root_.ThreeSum.BlockIndexedQuery.suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)









theorem leftPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u) (_root_.ThreeSum.BlockIndexedQuery.querySet k Q) := by
  exact (Finset.disjoint_map _).mpr (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl (_root_.ThreeSum.BlockRows.prefixIndices J k) u Q)

theorem rightPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u) (_root_.ThreeSum.BlockIndexedQuery.querySet k Q) := by
  exact (Finset.disjoint_map _).mpr
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_disjoint_compl (_root_.ThreeSum.BlockRows.prefixIndices J k) (fun i => Q i \ u i) Q)

theorem querySet_subset_suffix {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.BlockIndexedQuery.querySet k Q ⊆ _root_.ThreeSum.SubsetStages.suffix (J*L) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J L k) := by
  rw [← _root_.ThreeSum.BlockIndexedQuery.index_suffixDomain hk]
  exact (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_subset _ _).mpr (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_subset _ (fun _ _ => Finset.subset_univ _))

theorem leftPrefix_card {J L h k : ℕ} (hk : k ≤ J) (u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, (u i).card = h) : (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u).card = k*h := by
  rw [_root_.ThreeSum.BlockIndexedQuery.leftPrefix,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.prefixLeft,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ hu,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]

theorem rightPrefix_card {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u).card = k*h := by
  have hc : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, (Q i \ u i).card = h := by
    intro i hi
    rw [Finset.card_sdiff_of_subset (hu i hi).1,hQ i,(hu i hi).2]
    omega
  rw [_root_.ThreeSum.BlockIndexedQuery.rightPrefix,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.prefixRight,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ hc,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]

theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (_root_.ThreeSum.BlockIndexedQuery.querySet k Q).card = (J-k)*(2*h) := by
  rw [_root_.ThreeSum.BlockIndexedQuery.querySet,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.indexSet_card,_root_.ThreeSum.BlockForced.remaining,_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.prefixIndices_card hk]

section

private theorem private_c26fa15725_sizes_le {J h k : ℕ} (hk : k ≤ J) : k*h+(J-k)*(2*h) ≤ 2*h*J := by
  calc
    _ ≤ k*(2*h)+(J-k)*(2*h) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left k (by omega)) _
    _ = (k+(J-k))*(2*h) := (Nat.add_mul _ _ _).symm
    _ = _ := by rw [Nat.add_sub_of_le hk]; ring
end


theorem left_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, (u i).card = h) :
    (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k u ∪ _root_.ThreeSum.BlockIndexedQuery.querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_disjoint_query k Q u),
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_card hk u hu,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk Q hQ]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.private_c26fa15725_sizes_le hk

theorem right_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k Q u ∪ _root_.ThreeSum.BlockIndexedQuery.querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightPrefix_disjoint_query k Q u),
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightPrefix_card hk Q u hQ hu,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk Q hQ]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.private_c26fa15725_sizes_le hk

section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]





theorem leftWeights_le_card {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights o P B b S ≤ B.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.leftWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ B, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem rightWeights_le_card {h J : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (S : Finset (_root_.ThreeSum.BlockRows.Coord J (464*h))) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights o P d C c S ≤ C.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.rightWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ C, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem leftSource_abs_le {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (S : Finset (Fin (J*(464*h)))) : |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource P B b q S| ≤ B.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource _root_.ThreeSum.SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftWeights_le_card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P B b _

theorem rightSource_abs_le {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (S : Finset (Fin (J*(464*h)))) : |_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource P d C c q S| ≤ C.card := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource _root_.ThreeSum.SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightWeights_le_card (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) P d C c _



theorem queryValue_eq_transformPrefixValue {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J)
    (u : Fin J → Finset (Fin (464*h))) (hk : k ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue P d B C b c q k u =
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue P d B C b c q (_root_.ThreeSum.BlockRows.prefixIndices J k) u := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue _root_.ThreeSum.SubsetStages.stageValue
  rw [← _root_.ThreeSum.BlockIndexedQuery.index_suffixDomain hk]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SubsetTransport.mobius_partial_product_map (_root_.ThreeSum.BlockIndex.coordEquiv J (464*h)) _ _ _ _ _ _



end Histograms

end ThreeSum.BlockIndexedQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual sparse-query machine returns the original raw prefix mass

All coordinate transport, prefix sizes, source bounds, and cutoff facts
are discharged for the concrete block histograms. The remaining storage
premises are precisely the arrays produced by source and box preprocessing.
-/

namespace ThreeSum.LightBlockQuery
open _root_.ThreeSum.LightBlockQuery


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
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

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem sourceCut_le_width (h J : ℕ) : _root_.ThreeSum.LightBlockQuery.sourceCut h J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J := by
  have hh : 2*h ≤ 464*h := by omega
  simpa only [_root_.ThreeSum.LightBlockQuery.sourceCut,_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width,Nat.mul_comm] using Nat.mul_le_mul_right J hh

section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem queryValue_eq_prefixQuery {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k ≤ J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod + _root_.ThreeSum.RawIncidences.lift w.2.1*pMod + shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue pMod shift B C b c w.2.2 k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) =
      ((_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) : ℤ) := by
  calc
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.transformPrefixValue pMod shift B C b c w.2.2 (_root_.ThreeSum.BlockRows.prefixIndices J k) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) :=
      _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.queryValue_eq_transformPrefixValue pMod shift B C b c w.2.2 (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) hk
    _ = _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue pMod shift A B C a b c w k pre := by
      simp [_root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue,hp,hkey]
    _ = _ := _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.storedQueryValue_eq_prefixQuery pMod shift A B C a b c w pre hk





end OriginalIndices

end ThreeSum.LightBlockQuery

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local suffix coordinates with exact global source semantics

The remaining ambient ground set has width V, whereas source transforms use
the original width W. A contiguous shift embeds local box masks into global
source masks. Enumeration and box-table addresses can therefore use V without
changing the original raw-incidence query.
-/

namespace ThreeSum.ReportingHostSuffix
open _root_.ThreeSum.ReportingHostSuffix


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.StoredReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open scoped _root_.BigOperators







@[simp] theorem liftSet_card {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V)) :
    (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card = S.card := Finset.card_map _













@[simp] theorem mem_lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W))
    (i : Fin V) : i ∈ _root_.ThreeSum.ReportingHostSuffix.lowerSet hfit Q ↔ _root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit i ∈ Q := by
  simp [_root_.ThreeSum.ReportingHostSuffix.lowerSet]

theorem lift_lowerSet {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin W))
    (hQ : ∀ i ∈ Q, offset ≤ i.val ∧ i.val < offset+V) : _root_.ThreeSum.ReportingHostSuffix.liftSet hfit (_root_.ThreeSum.ReportingHostSuffix.lowerSet hfit Q) = Q := by
  ext i
  constructor
  · intro hi
    obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hi
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.mem_lowerSet hfit Q j).mp hj
  · intro hi
    have hb := hQ i hi
    let j : Fin V := ⟨i.val-offset,by omega⟩
    have he : _root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit j = i := by
      apply Fin.ext
      change offset+(i.val-offset)=i.val
      omega
    exact Finset.mem_map.mpr ⟨j,(_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.mem_lowerSet hfit Q j).mpr (he.symm ▸ hi),he⟩













theorem block_query_in_range {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (i : Fin (J*L)) (hi : i ∈ _root_.ThreeSum.BlockIndexedQuery.querySet k Q) : k*L ≤ i.val ∧ i.val < k*L+(J-k)*L := by
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetStages.mem_suffix i).mp (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_subset_suffix hk Q hi)
  have he : J*L-(J-k)*L = k*L := by rw [← Nat.sub_mul,Nat.sub_sub_self hk]
  constructor
  · simpa only [_root_.ThreeSum.BlockIndexedQuery.suffixStage,he] using hs
  · rw [← Nat.add_mul,Nat.add_sub_of_le hk]
    exact i.isLt



theorem lift_localQuery {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    _root_.ThreeSum.ReportingHostSuffix.liftSet (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum.ReportingHostSuffix.localQuery hk Q) = _root_.ThreeSum.BlockIndexedQuery.querySet k Q :=
  _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.lift_lowerSet (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) _ (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.block_query_in_range hk Q)

theorem localQuery_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (_root_.ThreeSum.ReportingHostSuffix.localQuery hk Q).card = (J-k)*(2*h) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card (_root_.ThreeSum.ReportingHostSuffix.block_fit hk),_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.lift_localQuery,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.querySet_card hk Q hQ]

section Original

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
open _root_.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences
open _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting
open _root_.ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts



end Original
end ThreeSum.ReportingHostSuffix

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
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
open _root_.ThreeSum.LightBlockQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed.program_meets__implementation_c6fc53ca04
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : _root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.Wanted h J α)
    (pre : List (Finset (Fin (464*h)))) (hk : k ≤ J) (hp : _root_.ThreeSum1960614.Machine.ThreeSum.StoredReporting.ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J ∣
      (a w.1 % pMod+_root_.ThreeSum.RawIncidences.lift w.2.1*pMod+shift)-_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.LightBlockQuery.sourceCut h J) ≤ maskBase)
    (hdataBox : boxBase+(_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k+1)*_root_.ThreeSum.SubsetAddress.downsetCap (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J)+(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) ≤ lim.space)
    (hword : (((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1)*2^(_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k)
      (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k+1) (hboxCut : boxCut ≤ _root_.ThreeSum.LightBlockQuery.residualSize h J k)
    (hflags : _root_.ThreeSum.LightBlockQuery.residualSize h J k-t ≤ boxCut)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR (_root_.ThreeSum.LightBlockQuery.sourceCut h J)
      (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J))
    (hstoredBox : _root_.ThreeSum.LightBoxStages.StoredThrough μ boxBase boxCut
      (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixBoxes.localLeaf hk pMod shift B C b c w.2.2 pre) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k))
    (hd : depth+_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J+10 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost.program 30 depth
      [_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J,_root_.ThreeSum.LightBlockQuery.sourceCut h J,_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*h,
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),k*h,
        _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre)),
        _root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k,k*(464*h),_root_.ThreeSum.LightBlockQuery.residualSize h J k,_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndexedQuery.querySet k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)),
        t,baseL,baseR,boxCut,boxBase,maskBase,work]
      μ (_root_.ThreeSum.LightReportingSuffixQueryHost.time (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.width h J) (_root_.ThreeSum.BlockIndexedQuery.suffixStage J (464*h) k) (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t)
      (fun r μ' =>
        r = (_root_.ThreeSum1960614.Machine.ThreeSum.RawReporting.prefixQuery (_root_.ThreeSum1960614.Machine.ThreeSum.RawIncidences.rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work maskBase (_root_.ThreeSum.LightSparseQuery.queryItems (_root_.ThreeSum.LightBlockQuery.residualSize h J k) t)) := by
  have hQ : ∀ i, (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2 i).card = 2*h :=
    fun i => _root_.ThreeSum.LayerCounts.mem_vertices.mp (w.2.2 i).2.property
  have hu : ∀ i ∈ _root_.ThreeSum.BlockRows.prefixIndices J k,
      _root_.ThreeSum.StoredReporting.prefixRows (J := J) pre i ⊆ _root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2 i ∧ (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre i).card = h := by
    intro i hi
    exact hp.2 i (_root_.ThreeSum1960614.Machine.ThreeSum.BlockRows.mem_prefixIndices.mp hi)
  have hLc := _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_card hk (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) (fun i hi => (hu i hi).2)
  have hRc := _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightPrefix_card hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre) hQ hu
  have hQc : (_root_.ThreeSum.ReportingHostSuffix.localQuery hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)).card = _root_.ThreeSum.LightBlockQuery.residualSize h J k := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.localQuery_card hk _ hQ
  have hlocal := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.lift_localQuery hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2)
  have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryHost.program_meets (d := depth) (μ := μ) (cut := _root_.ThreeSum.LightBlockQuery.sourceCut h J)
    (_root_.ThreeSum.ReportingHostSuffix.block_fit hk) (_root_.ThreeSum.ReportingHostSuffix.localQuery hk (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2))
    (_root_.ThreeSum.BlockIndexedQuery.leftPrefix k (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum.BlockIndexedQuery.rightPrefix k (_root_.ThreeSum1960614.Machine.ThreeSum.BlockForced.outputRows w.2.2) (_root_.ThreeSum.StoredReporting.prefixRows (J := J) pre))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource pMod B b w.2.2) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource pMod shift C c w.2.2)
    hw (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.sourceCut_le_width h J) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.suffixStage_le J (464*h) k) hdataL hdataR hdataBox
    (by simpa only [hQc] using hmasks) hspace hword (by simpa only [hQc, _root_.ThreeSum.BlockIndexedQuery.suffixStage] using hvalueWord)
    (by simpa only [hQc] using ht) (by simpa only [hQc] using hboxCut) (by simpa only [hQc] using hflags)
    (by rw [hlocal]; exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftPrefix_disjoint_query k _ _)
    (by rw [hlocal]; exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightPrefix_disjoint_query k _ _)
    (by rw [hlocal]; exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.left_union_card_le hk _ _ hQ (fun i hi => (hu i hi).2))
    (by rw [hlocal]; exact _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.right_union_card_le hk _ _ hQ hu)
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource_abs_le pMod B b w.2.2 S)
    (fun S _ => _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource_abs_le pMod shift C c w.2.2 S)
    hstoredL hstoredR hstoredBox hd
  rw [hLc,hRc,hQc,hlocal] at hc
  exact hc.mono le_rfl (fun r μ' ⟨hr,hkeep⟩ =>
    ⟨hr.trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockQuery.queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey),hkeep⟩)
end

end

theorem solution.{u_implementation_0,u_implementation_1,u_implementation_2} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed.program_meets__implementation_c6fc53ca04.{u_implementation_0,u_implementation_1,u_implementation_2}) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQueryIndexed.program_meets__implementation_c6fc53ca04.{u_implementation_0,u_implementation_1,u_implementation_2})

#print axioms solution
