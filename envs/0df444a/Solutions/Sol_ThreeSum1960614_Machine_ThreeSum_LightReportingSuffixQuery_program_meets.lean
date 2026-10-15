-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:33:34.435803+00:00
-- url     : https://prove2.me/submissions/4dba3825-0517-4a12-9c06-b57ad0b3483d

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCanonicalBoxSum_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixExplicit_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSign_meets
import Theorems.Thm_ThreeSum_SparseBoxes_mem_explicitLeaves
import Theorems.Thm_ThreeSum_SparseBoxes_sparse_query_identity
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt
import Theorems.Thm_ThreeSum_SubsetStages_stageValue_abs_le

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
namespace ThreeSum.ExplicitLayers
end ThreeSum.ExplicitLayers
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCell
end ThreeSum.LightReportingSuffixCell
namespace ThreeSum.LightReportingSuffixQuery
end ThreeSum.LightReportingSuffixQuery
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.QueryCoordinates
end ThreeSum.QueryCoordinates
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostQueryBounds
end ThreeSum.ReportingHostQueryBounds
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SignedLeaf
end ThreeSum.SignedLeaf
namespace ThreeSum.SparseBoxes
end ThreeSum.SparseBoxes
namespace ThreeSum.StoredReporting
end ThreeSum.StoredReporting
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockForced
end ThreeSum1960614.Machine.ThreeSum.BlockForced
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
end ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.ExplicitLayers
end ThreeSum1960614.Machine.ThreeSum.ExplicitLayers
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
end ThreeSum1960614.Machine.ThreeSum.QueryCoordinates
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
end ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SignedLeaf
end ThreeSum1960614.Machine.ThreeSum.SignedLeaf
namespace ThreeSum1960614.Machine.ThreeSum.SparseBoxes
end ThreeSum1960614.Machine.ThreeSum.SparseBoxes
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Finite sparse-query boxes

The largest-missing-element partition and the reusable box recurrence are proved
here as exact finite identities.  The accompanying cardinalities concern the
actual canonical box family, not the family of all arbitrary free-coordinate
subsets.
-/

namespace ThreeSum.SparseBoxes
open _root_.ThreeSum.SparseBoxes


open scoped _root_.BigOperators

variable {α : Type*} [LinearOrder α]

























/-! ## Canonical free prefixes and the finite preprocessing family -/



































/-! ## The exact addition recurrence and query sum -/





















/-! ## Number of query accesses -/





theorem explicitLeaves_eq_filter (q : Finset α) (t : ℕ) :
    _root_.ThreeSum.SparseBoxes.explicitLeaves q t = q.powerset.filter (fun leaf => (q \ leaf).card < t) := by
  ext leaf
  simp only [_root_.ThreeSum.SparseBoxes.mem_explicitLeaves, Finset.mem_filter, Finset.mem_powerset]





/-- Query identity using the cardinality-layer enumeration of explicit leaves. -/
theorem sparse_query_identity_enumerated (q : Finset α) (t : ℕ)
    (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ _root_.ThreeSum.SparseBoxes.explicitLeaves q t, weight leaf) +
      ∑ u ∈ q.powersetCard t, _root_.ThreeSum.SparseBoxes.boxSum (q \ u) (_root_.ThreeSum.SparseBoxes.queryFree q u) weight := by
  simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SparseBoxes.explicitLeaves_eq_filter] using _root_.ThreeSum.SparseBoxes.sparse_query_identity q t weight

end ThreeSum.SparseBoxes

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Compact addresses for bounded-cardinality bit masks

Both ranking and enumeration recurse on the highest available bit. The
enumerator stops immediately when the requested layer is empty. In
particular, it does not enumerate the ambient Boolean cube and filter it.
-/

namespace ThreeSum.SubsetAddress
open _root_.ThreeSum.SubsetAddress


set_option maxRecDepth 4000

open _root_.Finset
open scoped _root_.BigOperators

















































theorem layerOffset_succ (L k : ℕ) :
    _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) = _root_.ThreeSum.SubsetAddress.layerOffset L k + L.choose k := by
  exact Finset.sum_range_succ _ _

theorem layerOffset_mono (L : ℕ) : Monotone (_root_.ThreeSum.SubsetAddress.layerOffset L) := by
  apply monotone_nat_of_le_succ
  intro k
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  omega





theorem downsetRank_lt {L cut m : ℕ} (hm : m < 2 ^ L) (hk : _root_.ThreeSum.SubsetAddress.weight L m ≤ cut) :
    _root_.ThreeSum.SubsetAddress.downsetRank L m < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hmask : _root_.ThreeSum.SubsetAddress.IsMask L (_root_.ThreeSum.SubsetAddress.weight L m) m := ⟨hm, rfl⟩
  have hr := _root_.ThreeSum.SubsetAddress.layerRank_lt hmask
  unfold _root_.ThreeSum.SubsetAddress.downsetRank _root_.ThreeSum.SubsetAddress.downsetCap
  calc
    _ < _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m) + L.choose (_root_.ThreeSum.SubsetAddress.weight L m) := Nat.add_lt_add_left hr _
    _ = _root_.ThreeSum.SubsetAddress.layerOffset L (_root_.ThreeSum.SubsetAddress.weight L m + 1) := (_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L _).symm
    _ ≤ _ := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_mono L (Nat.succ_le_succ (le_min hk hmask.le_width))





















































theorem subsetRank_lt {L cut : ℕ} {s : Finset (Fin L)} (hs : s.card ≤ cut) :
    _root_.ThreeSum.SubsetAddress.subsetRank s < _root_.ThreeSum.SubsetAddress.downsetCap L cut := by
  have hm := _root_.ThreeSum.SubsetAddress.subsetMask_isMask s
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.downsetRank_lt hm.1 (hm.2.trans_le hs)











end ThreeSum.SubsetAddress

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

/-- From a theorem about a body to the specification. -/
theorem Meets.of_body {args : List ℤ} {Q : ℤ → (ℕ → ℤ) → Prop} {body : _root_.ThreeSum1960614.Machine.Light.Stmt}
    (hp : P[p]? = some body)
    (h : _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨_root_.Light.frame args, μ⟩ T fun σ' => Q (σ'.loc 0) σ'.mem) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d args μ T Q :=
  ⟨body, hp, h⟩









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





































theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he



















theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (_root_.ThreeSum.QueryCoordinates.missingSets Q k).Nodup := by
  unfold _root_.ThreeSum.QueryCoordinates.missingSets
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.setLayer_nodup _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp ha
  have hbs := (_root_.ThreeSum.QueryCoordinates.mem_setLayer _ (List.nodup_reverse.mpr (_root_.ThreeSum.QueryCoordinates.positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,_root_.ThreeSum.QueryCoordinates.positions_toFinset] at has hbs
  have h := congrArg _root_.ThreeSum.SubsetAddress.natPositions he
  rw [_root_.ThreeSum.QueryCoordinates.decode_maskOf (has.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q)),
      _root_.ThreeSum.QueryCoordinates.decode_maskOf (hbs.1.trans (_root_.ThreeSum.SubsetAddress.natPositions_subset Q))] at h
  exact h





end ThreeSum.QueryCoordinates

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Signed leaf weights and the explicit part of sparse queries

The alternating sign is separated from the query cardinality, allowing
the same leaf weights to be used in stored boxes and direct leaf reads.
-/

namespace ThreeSum.SignedLeaf
open _root_.ThreeSum.SignedLeaf


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators





theorem abs_value_le {W cut B C : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR S : Finset (Fin W))
    (hstage : stage ≤ W) (hL : (preL ∪ S).card ≤ cut) (hR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ C) :
    |_root_.ThreeSum.SignedLeaf.value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*C) : ℕ) : ℤ) := by
  rw [_root_.ThreeSum.SignedLeaf.value,abs_mul,abs_neg_one_pow,one_mul,abs_mul]
  have h₁ := _root_.ThreeSum.SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hL
  have h₂ := _root_.ThreeSum.SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hR
  simpa only [Nat.cast_mul] using mul_le_mul h₁ h₂ (abs_nonneg _) (Int.natCast_nonneg _)

theorem neg_one_pow_sub {a b : ℕ} (h : b ≤ a) :
    (-1 : ℤ)^(a-b) = (-1 : ℤ)^a*(-1 : ℤ)^b := by
  have ha : a = (a-b)+b := by omega
  rw [ha,pow_add,mul_assoc,← pow_add]
  have hb : b+b = 2*b := by omega
  rw [hb,pow_mul]
  norm_num

theorem mobius_eq_signed_sum {W : ℕ} (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (preL preR Q : Finset (Fin W)) :
    _root_.ThreeSum.Subset.mobius
      (fun S => _root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S)*
        _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S)) Q =
      (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, _root_.ThreeSum.SignedLeaf.value f g stage preL preR S := by
  rw [_root_.ThreeSum.Subset.mobius,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.neg_one_pow_sub (Finset.card_le_card (Finset.mem_powerset.mp hS)),_root_.ThreeSum.SignedLeaf.value]
  ring





@[simp] theorem mem_explicitMissing {W : ℕ} (Q U : Finset (Fin W)) (t : ℕ) :
    U ∈ _root_.ThreeSum.SignedLeaf.explicitMissing Q t ↔ U ⊆ Q ∧ U.card < t := by
  simp only [_root_.ThreeSum.SignedLeaf.explicitMissing,List.mem_flatMap,List.mem_range,_root_.ThreeSum.QueryCoordinates.missingSets_mem]
  constructor
  · rintro ⟨j,hj,hU,hcard⟩
    exact ⟨hU,by omega⟩
  · rintro ⟨hU,ht⟩
    exact ⟨U.card,ht,hU,rfl⟩

theorem explicitMissing_nodup {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (_root_.ThreeSum.SignedLeaf.explicitMissing Q t).Nodup := by
  rw [_root_.ThreeSum.SignedLeaf.explicitMissing,List.nodup_flatMap]
  constructor
  · intro j hj
    exact _root_.ThreeSum1960614.Machine.ThreeSum.QueryCoordinates.missingSets_nodup Q j
  · refine (List.nodup_range (n := t)).imp ?_
    intro a b hab
    apply List.disjoint_left.mpr
    intro U hU hV
    have h₁ := (_root_.ThreeSum.QueryCoordinates.missingSets_mem Q U a).mp hU
    have h₂ := (_root_.ThreeSum.QueryCoordinates.missingSets_mem Q U b).mp hV
    omega

theorem explicitLeaves_nodup {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (_root_.ThreeSum.SignedLeaf.explicitLeaves Q t).Nodup := by
  apply (_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.explicitMissing_nodup Q t).map_on
  intro A hA B hB he
  have ha := (_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitMissing Q A t).mp hA
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitMissing Q B t).mp hB
  have hh := congrArg (fun U => Q \ U) he
  rwa [Finset.sdiff_sdiff_eq_self ha.1,Finset.sdiff_sdiff_eq_self hb.1] at hh

theorem mem_explicitLeaves {W : ℕ} (Q S : Finset (Fin W)) (t : ℕ) :
    S ∈ _root_.ThreeSum.SignedLeaf.explicitLeaves Q t ↔ S ⊆ Q ∧ (Q \ S).card < t := by
  constructor
  · intro h
    obtain ⟨U,hU,rfl⟩ := List.mem_map.mp h
    have hu := (_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitMissing Q U t).mp hU
    exact ⟨Finset.sdiff_subset,by rw [Finset.sdiff_sdiff_eq_self hu.1]; exact hu.2⟩
  · rintro ⟨hS,ht⟩
    exact List.mem_map.mpr ⟨Q \ S,(_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitMissing Q _ t).mpr ⟨Finset.sdiff_subset,ht⟩,
      Finset.sdiff_sdiff_eq_self hS⟩

end ThreeSum.SignedLeaf

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Exact values and sizes of the explicitly evaluated missing layers -/

namespace ThreeSum.ExplicitLayers
open _root_.ThreeSum.ExplicitLayers


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators















theorem valueSum_eq_explicit {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    _root_.ThreeSum.ExplicitLayers.valueSum Q weight t = ∑ S ∈ _root_.ThreeSum.SparseBoxes.explicitLeaves Q t, weight S := by
  have he : (_root_.ThreeSum.SignedLeaf.explicitLeaves Q t).toFinset = _root_.ThreeSum.SparseBoxes.explicitLeaves Q t := by
    ext S
    simp only [List.mem_toFinset,_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mem_explicitLeaves,_root_.ThreeSum.SparseBoxes.mem_explicitLeaves]
  rw [_root_.ThreeSum.ExplicitLayers.valueSum,← List.sum_toFinset weight (_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.explicitLeaves_nodup Q t),he]

theorem sparse_identity {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    (∑ S ∈ Q.powerset, weight S) = _root_.ThreeSum.ExplicitLayers.valueSum Q weight t+
      ∑ U ∈ Q.powersetCard t, _root_.ThreeSum.SparseBoxes.boxSum (Q \ U) (_root_.ThreeSum.SparseBoxes.queryFree Q U) weight := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ExplicitLayers.valueSum_eq_explicit]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.SparseBoxes.sparse_query_identity_enumerated Q t weight

end ThreeSum.ExplicitLayers

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Output bounds and stored-table preservation for actual query batching -/

namespace ThreeSum.ReportingHostQueryBounds
open _root_.ThreeSum.ReportingHostQueryBounds


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators







theorem boxStored_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ} {f : Finset (Fin W) → ℤ}
    (h : _root_.ThreeSum.LightBoxStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut → μ' i = μ i) :
    _root_.ThreeSum.LightBoxStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)

end ThreeSum.ReportingHostQueryBounds

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

















theorem sum_powerset_lift {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (f : Finset (Fin W) → ℤ) :
    (∑ S ∈ (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).powerset, f S) = ∑ S ∈ Q.powerset, f (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S) := by
  simp only [_root_.ThreeSum.ReportingHostSuffix.liftSet,Finset.map_eq_image]
  rw [Finset.powerset_image,Finset.sum_image]
  intro A _ B _ he
  exact (Finset.image_inj (_root_.ThreeSum.ReportingHostSuffix.shiftEmbedding offset hfit).injective).mp he





theorem leafWeight_abs_le {W V offset sourceCut stage B D : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (preL preR : Finset (Fin W)) (S : Finset (Fin V))
    (hstage : stage ≤ W) (hL : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card ≤ sourceCut)
    (hR : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D) :
    |_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.abs_value_le f g stage preL preR _ hstage hL hR hf hg

theorem query_eq_local_signed_sum {W V offset : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (preL preR : Finset (Fin W)) (Q : Finset (Fin V)) :
    _root_.ThreeSum.Subset.mobius (fun S => _root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S)*
      _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S)) (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q) =
        (-1 : ℤ)^Q.card * ∑ S ∈ Q.powerset, _root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.mobius_eq_signed_sum,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.sum_powerset_lift,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card]
  rfl











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

namespace ThreeSum1960614.Machine

/-!
# A concrete box-leaf cell with global source and local box addresses

Multiplication lifts the local mask into the global suffix. The actual source
reader uses width W; a second actual compact-address computation uses width V.
Only the local compact box cell and polynomial scratch are modified.
-/

namespace ThreeSum.LightReportingSuffixCell
open _root_.ThreeSum.LightReportingSuffixCell


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}





theorem small_word {W V : ℕ} (hV : V ≤ W)
    (hw : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    (((V+1)*2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
  have hm := Nat.mul_le_mul (Nat.succ_le_succ hV)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.succ_le_succ hV))
  exact (by exact_mod_cast hm : (((V+1)*2^(V+1) : ℕ) : ℤ) ≤
    (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hw

theorem small_space {W V work : ℕ} (hV : V ≤ W)
    (hs : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space) :
    work+_root_.ThreeSum.LightPascal.tableSize V+(V+1) ≤ lim.space := by
  have hp := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
  change (V+1)^2 ≤ (W+1)^2 at hp
  unfold _root_.ThreeSum.LightPascal.tableSize at *
  omega









end ThreeSum.LightReportingSuffixCell

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingSuffixQuery
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostSuffix
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
open scoped _root_.BigOperators
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program_meets__implementation_130a88f74b
    {μ : ℕ → ℤ} {W V offset cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(V+1)*_root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.LightSparseQuery.queryItems Q.card t ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (_root_.ThreeSum.LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q)) (hdisjR : Disjoint preR (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q))
    (hcardL : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : _root_.ThreeSum.LightBoxStages.StoredThrough μ boxBase boxCut
      (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) V)
    (hd : d+W+9 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program 28 d
      [W,cut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,V,2^offset,
        Q.card,_root_.ThreeSum.SubsetAddress.subsetMask Q,t,baseL,baseR,boxCut,boxBase,maskBase,work] μ (_root_.ThreeSum.LightReportingSuffixQuery.time W V Q.card t)
      (fun r μ' =>
        r = _root_.ThreeSum.Subset.mobius (fun S => _root_.ThreeSum.SubsetStages.stageValue f stage (preL ∪ S)*
          _root_.ThreeSum.SubsetStages.stageValue g stage (preR ∪ S)) (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit Q) ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' work maskBase (_root_.ThreeSum.LightSparseQuery.queryItems Q.card t)) := by
  have hV : V ≤ W := by omega
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have hboxV : boxCut ≤ V := hboxCut.trans hQcard
  have hoff : _root_.ThreeSum.SubsetAddress.layerOffset Q.card t ≤ _root_.ThreeSum.LightSparseQuery.queryItems Q.card t := by
    unfold _root_.ThreeSum.LightSparseQuery.queryItems; omega
  have hchoose : Q.card.choose t ≤ _root_.ThreeSum.LightSparseQuery.queryItems Q.card t := by
    unfold _root_.ThreeSum.LightSparseQuery.queryItems; omega
  have hproduct : (2^stage*B)*(2^stage*D) ≤ 2^V*((2^stage*B)*(2^stage*D)) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos V)
  have hfullBound : 2^V*((2^stage*B)*(2^stage*D)) ≤ _root_.ThreeSum.LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.le_mul_of_pos_left _ (by unfold _root_.ThreeSum.LightSparseQuery.queryItems; omega)
  have heBound : (_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) ≤
      _root_.ThreeSum.LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.mul_le_mul (Nat.succ_le_succ hoff) hproduct
  have hbBound : Q.card.choose t*(2^V*((2^stage*B)*(2^stage*D))) ≤
      _root_.ThreeSum.LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.mul_le_mul_right _ (hchoose.trans (Nat.le_succ _))
  have hExplicitWord : (((_root_.ThreeSum.SubsetAddress.layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast heBound : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
      (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ)).trans hvalueWord
  have hBoxWord : ((Q.card.choose t*(2^V*((2^stage*B)*(2^stage*D))) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbBound : ((Q.card.choose t*(2^V*((2^stage*B)*(2^stage*D))) : ℕ) : ℤ) ≤
      (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ)).trans hvalueWord
  have hCL : preL.card+Q.card ≤ cut := by
    simpa only [Finset.card_union_of_disjoint hdisjL,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card] using hcardL
  have hCR : preR.card+Q.card ≤ cut := by
    simpa only [Finset.card_union_of_disjoint hdisjR,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card] using hcardR
  have hweight (S : Finset (Fin V)) (hS : S.card ≤ Q.card) :
      |_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    apply _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.leafWeight_abs_le (sourceCut := cut) hfit f g preL preR S hstage
    · have he := Finset.card_union_le preL (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S)
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card] at he
      exact he.trans (by omega)
    · have he := Finset.card_union_le preR (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S)
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card] at he
      exact he.trans (by omega)
    · exact hf
    · exact hg
  have htotal : |∑ S ∈ Q.powerset, _root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤ lim.word := by
    have hs : |∑ S ∈ Q.powerset, _root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤
        ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by
      calc
        _ ≤ ∑ S ∈ Q.powerset, |_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _S ∈ Q.powerset, (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
          Finset.sum_le_sum fun S hS => hweight S (Finset.card_le_card (Finset.mem_powerset.mp hS))
        _ = _ := by simp [Nat.cast_mul]
    have hn : 2^Q.card*((2^stage*B)*(2^stage*D)) ≤ _root_.ThreeSum.LightSparseQuery.magnitudeBound V stage Q.card t B D :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hQcard)).trans hfullBound
    have hz : ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
        (_root_.ThreeSum.LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) := by exact_mod_cast hn
    exact hs.trans (hz.trans hvalueWord)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 28) (by rfl : program[28]? = some (body 27 2 22))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.body _root_.ThreeSum.LightReportingSuffixQuery.time
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixExplicit.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program) (pMain := 27) (d := d+1) (μ := μ) (t := t)
    (baseL := baseL) (baseR := baseR) (maskBase := maskBase) (work := work)
    rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.explicitProcs hfit Q preL preR f g hw hcut hstage hdataL hdataR (by omega) hspace hword
    hExplicitWord ht hcardL hcardR hf hg hstoredL hstoredR (by omega)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (he _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen he ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro explicit μ₁ ⟨heValue, hkeepE⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hstoredBox₁ := _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostQueryBounds.boxStored_of_on hstoredBox (by
    intro i _ hi
    have ha := hi.trans_le hdataBox
    exact hkeepE i ⟨by omega,Or.inl ha⟩)
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightCanonicalBoxSum.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program) (pMain := 2) (d := d+1) (μ := μ₁) (t := t)
    (base := boxBase) (maskBase := maskBase) (work := work)
    rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.boxProcs Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) hw hboxV hdataBox (by omega)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.small_space hV hspace) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.small_word hV hword)
    hBoxWord ht hflags (fun S hS => hweight S (hS.trans hboxCut)) hstoredBox₁ (by omega)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hb _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hb ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     on_goal -1 => (rintro boxes μ₂ ⟨hbValue, hkeepB⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hsum : explicit+boxes = ∑ S ∈ Q.powerset, _root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S := by
    rw [heValue,hbValue]
    exact (_root_.ThreeSum1960614.Machine.ThreeSum.ExplicitLayers.sparse_identity Q (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) t).symm
  have htotalSides := abs_le.mp htotal
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (∑ S ∈ Q.powerset, _root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsum]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hsum] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsum] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightSign.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program) (pMain := 22) (d := d+1) (μ := μ₂)
    (e := Q.card) rfl hw (by omega) htotal
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hs _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hs ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSign.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSign.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSign.time] <;> omega)
     on_goal -1 => (rintro res μ₃ ⟨hres, hmem⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst μ₃
  refine ⟨hres.trans (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.query_eq_local_signed_sum hfit f g stage preL preR Q).symm,?_⟩
  intro i hi
  exact (hkeepB i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩).trans
    (hkeepE i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩)
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program_meets__implementation_130a88f74b) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixQuery.program_meets__implementation_130a88f74b)

#print axioms solution
