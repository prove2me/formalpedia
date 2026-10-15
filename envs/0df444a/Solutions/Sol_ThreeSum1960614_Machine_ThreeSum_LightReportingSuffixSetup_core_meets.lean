-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.core_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:35:16.384353+00:00
-- url     : https://prove2.me/submissions/668b7ea4-b172-41b4-be17-13d289acf6b9

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBoxStages_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightReportingSuffixTable_meets
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
namespace ThreeSum.LightBlockQuery
end ThreeSum.LightBlockQuery
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingSuffixCell
end ThreeSum.LightReportingSuffixCell
namespace ThreeSum.LightReportingSuffixSetup
end ThreeSum.LightReportingSuffixSetup
namespace ThreeSum.LightSignedLeafBatch
end ThreeSum.LightSignedLeafBatch
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LightZetaCell
end ThreeSum.LightZetaCell
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.RawIncidences
end ThreeSum.RawIncidences
namespace ThreeSum.ReportingHostSuffix
end ThreeSum.ReportingHostSuffix
namespace ThreeSum.SignedLeaf
end ThreeSum.SignedLeaf
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
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
end ThreeSum1960614.Machine.ThreeSum.LightBlockQuery
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup
end ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup
namespace ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
end ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaCell
end ThreeSum1960614.Machine.ThreeSum.LightZetaCell
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.RawIncidences
end ThreeSum1960614.Machine.ThreeSum.RawIncidences
namespace ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
end ThreeSum1960614.Machine.ThreeSum.RawPrefixCounts
namespace ThreeSum1960614.Machine.ThreeSum.RawReporting
end ThreeSum1960614.Machine.ThreeSum.RawReporting
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
end ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix
namespace ThreeSum1960614.Machine.ThreeSum.SignedLeaf
end ThreeSum1960614.Machine.ThreeSum.SignedLeaf
namespace ThreeSum1960614.Machine.ThreeSum.StoredReporting
end ThreeSum1960614.Machine.ThreeSum.StoredReporting
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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

















end ThreeSum.SignedLeaf

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Initial signed-product table writes on one actual mask layer -/

namespace ThreeSum.LightSignedLeafBatch
open _root_.ThreeSum.LightSignedLeafBatch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaCell
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaCell
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}

theorem storedThrough_of_on {W cut base : ℕ} {μ μ' : ℕ → ℤ}
    {f : Finset (Fin W) → ℤ}
    (h : _root_.ThreeSum.LightZetaStages.StoredThrough μ base cut f W)
    (hkeep : ∀ i, base ≤ i → i < base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut → μ' i = μ i) :
    _root_.ThreeSum.LightZetaStages.StoredThrough μ' base cut f W := by
  intro j hj S hS
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  simp only [Nat.succ_mul] at hm
  have he := hkeep (base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.subsetRank S) (by omega) (by
    simp only [Nat.succ_mul]
    omega)
  exact he.trans (h j hj S hS)















end ThreeSum.LightSignedLeafBatch

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























theorem leafWeight_abs_le {W V offset sourceCut stage B D : ℕ} (hfit : offset+V ≤ W)
    (f g : Finset (Fin W) → ℤ) (preL preR : Finset (Fin W)) (S : Finset (Fin V))
    (hstage : stage ≤ W) (hL : (preL ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card ≤ sourceCut)
    (hR : (preR ∪ _root_.ThreeSum.ReportingHostSuffix.liftSet hfit S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D) :
    |_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SignedLeaf.abs_value_le f g stage preL preR _ hstage hL hR hf hg













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

open _root_.ThreeSum.LightReportingSuffixSetup
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup

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
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.core_meets__implementation_1a2e59ecb3 {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(V+1)*_root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ work)
    (hspace : work+1+_root_.ThreeSum.LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : _root_.ThreeSum.LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+10 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.program 28 d
      [W,sourceCut,boxCut,stage,preL.card,_root_.ThreeSum.SubsetAddress.subsetMask preL,preR.card,_root_.ThreeSum.SubsetAddress.subsetMask preR,
        V,2^offset,baseL,baseR,boxBase,maskBase,work] μ (_root_.ThreeSum.LightReportingSuffixSetup.coreTime W V boxCut)
      (fun _ μ' =>
        _root_.ThreeSum.LightBoxStages.StoredThrough μ' boxBase boxCut (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) V ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ' maskBase boxBase ((V+1)*_root_.ThreeSum.SubsetAddress.downsetCap V boxCut)) := by
  have hV : V ≤ W := by omega
  have hcap : _root_.ThreeSum.SubsetAddress.downsetCap V boxCut ≤ (V+1)*_root_.ThreeSum.SubsetAddress.downsetCap V boxCut :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^stage*B)*(2^stage*D) ≤ 2^V*((2^stage*B)*(2^stage*D)) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    exact (by exact_mod_cast hh : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤
      ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ)).trans hvalueWord
  have hleafBound : ∀ S, S.card ≤ boxCut →
      |_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    intro S hS
    apply _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.leafWeight_abs_le (sourceCut := sourceCut) hfit f g preL preR S hstage
    · have he := Finset.card_union_le preL (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S)
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreL)
    · have he := Finset.card_union_le preR (_root_.ThreeSum.ReportingHostSuffix.liftSet hfit S)
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostSuffix.liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreR)
    · exact hf
    · exact hg
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 28) (by rfl : program[28]? = some (coreBody 27 2))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.coreBody _root_.ThreeSum.LightReportingSuffixSetup.coreTime
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixTable.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.program) (pMain := 27)
    (pEnumSetup := 3) (pEnum := 20) (pBatch := 26) (pCell := 25) (d := d+1) (μ := μ)
    rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.procs rfl rfl rfl rfl hfit preL preR f g hw hcut hboxCut hstage
    (by omega) (by omega) (by omega) hmasks (Or.inl hdataL) (Or.inl hdataR)
    hspace hword hproductWord hpreL hpreR hf hg hstoredL hstoredR (by omega)
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hl _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hl ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingSuffixTable.time, _root_.ThreeSum.LightBoxStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingSuffixTable.time, _root_.ThreeSum.LightBoxStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingSuffixTable.time, _root_.ThreeSum.LightBoxStages.time] <;> omega)
     on_goal -1 => (rintro leafRet μ₁ ⟨hleaves, hkeepLeaf⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBoxStages.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.program) (pMain := 2) (pSize := 9) (pPass := 21)
    (pEnumSetup := 3) (pEnum := 20) (pBatch := 22) (pCell := 23) (d := d+1) (μ := μ₁)
    rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.procs.size rfl rfl rfl rfl rfl _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.procs.setup _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.procs.offset _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.procs.erase
    (_root_.ThreeSum.ReportingHostSuffix.leafWeight hfit f g stage preL preR) hw hboxCut hbox hmasks
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.small_space hV hspace) (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixCell.small_word hV hword)
    hvalueWord hleaves hleafBound (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingSuffixTable.time, _root_.ThreeSum.LightBoxStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightReportingSuffixTable.time, _root_.ThreeSum.LightBoxStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingSuffixTable.time, _root_.ThreeSum.LightBoxStages.time] <;> omega)
     on_goal -1 => (rintro boxRet μ₂ ⟨hboxes, hkeepBox⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkept : _root_.ThreeSum1960614.Machine.Light.KeptBut μ μ₂ maskBase boxBase ((V+1)*_root_.ThreeSum.SubsetAddress.downsetCap V boxCut) := by
    intro i hi
    exact (hkeepBox i hi).trans (hkeepLeaf i ⟨hi.1,by omega⟩)
  refine ⟨hboxes,?_,?_,hkept⟩
  · apply _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredL
    intro i hi₀ hi₁
    exact hkept i ⟨by omega,Or.inl (by omega)⟩
  · apply _root_.ThreeSum1960614.Machine.ThreeSum.LightSignedLeafBatch.storedThrough_of_on hstoredR
    intro i hi₀ hi₁
    exact hkept i ⟨by omega,Or.inl (by omega)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.core_meets__implementation_1a2e59ecb3) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingSuffixSetup.core_meets__implementation_1a2e59ecb3)

#print axioms solution
