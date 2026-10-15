-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs.meets_with_masks
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:22:25.099439+00:00
-- url     : https://prove2.me/submissions/a467d45f-35a3-4b91-866c-7d0f024e29d7

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Definitions.Def_ThreeSum1962Source_Bundle07
import Definitions.Def_ThreeSum1962Source_Bundle08
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_GlobalKeyEnumeration_rawOutput_abs_le
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalKeys_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightRadixKeys_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LocalKeyArraySemantics_seg_flatMap_rows
import Theorems.Thm_ThreeSum_OneHotMask_eval_maskOf

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BlockCoefficientRows
end ThreeSum.BlockCoefficientRows
namespace ThreeSum.BlockIndex
end ThreeSum.BlockIndex
namespace ThreeSum.BlockRows
end ThreeSum.BlockRows
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightGlobalKeys
end ThreeSum.LightGlobalKeys
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalKeyArraySemantics
end ThreeSum.LocalKeyArraySemantics
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.OutputKeyMasks
end ThreeSum.OutputKeyMasks
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
end ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
namespace ThreeSum1960614.Machine.ThreeSum.BlockEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockIndex
end ThreeSum1960614.Machine.ThreeSum.BlockIndex
namespace ThreeSum1960614.Machine.ThreeSum.BlockRows
end ThreeSum1960614.Machine.ThreeSum.BlockRows
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
end ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalKeyArraySemantics
end ThreeSum1960614.Machine.ThreeSum.LocalKeyArraySemantics
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks
end ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
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
# Reading constructed block coefficients in the flat mask order

The imperative coefficient constructor writes rows. The mask evaluator reads
one flat array. These lemmas identify the two layouts, including empty ground
sets, and specialize them to the unchanged schedule-occurrence encoding.
-/

namespace ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.BlockCoefficientRows


open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds













@[simp] theorem mapRow_fin {h : ℕ} (b : Bool) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) (i : Fin (464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s.val i.val = (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h s (i,b)).val := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow,s.isLt,dite_true,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin]



theorem mapRow_le {h : ℕ} (b : Bool) {s i : ℕ}
    (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (hi : i < 464*h) : _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b s i ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_fin b ⟨s,hs⟩ ⟨i,hi⟩]
  exact Nat.le_of_lt (ZMod.val_lt _)







end ThreeSum.BlockCoefficientRows

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph
open _root_.ThreeSum.LocalMaskGraph


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.MaskDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskDecode
open scoped _root_.BigOperators







theorem maskAt_spec {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.IsMask L h (_root_.ThreeSum.LocalMaskGraph.maskAt L h i) := (_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h _).mp (_root_.ThreeSum.LocalMaskGraph.maskAt_mem hi)



theorem subsetMask_setAt {L h i : ℕ} (hi : i < _root_.ThreeSum.LocalMaskGraph.vertexCount L h) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.LocalMaskGraph.setAt L h i) = _root_.ThreeSum.LocalMaskGraph.maskAt L h i := _root_.ThreeSum.MaskDecode.subsetMask_decode (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_spec hi).1















end ThreeSum.LocalMaskGraph

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.GlobalKeyEnumeration


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
open scoped _root_.BigOperators

set_option maxHeartbeats 1800000













































theorem localKeys_bounded (h : ℕ) :
    ∀ x ∈ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h, |x| ≤ ((464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  exact _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.rawOutput_abs_le _ _



end ThreeSum.GlobalKeyEnumeration

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Local output keys from ordinary stored masks and coefficient rows

This identifies the two nonnegative masked sums used by the imperative
local-key program with the unchanged signed `GlobalEncoding.rawOutput`.
-/

namespace ThreeSum.OutputKeyMasks
open _root_.ThreeSum.OutputKeyMasks


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.OneHotMask
open _root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open scoped _root_.BigOperators

theorem extend_zero (L : ℕ) : _root_.ThreeSum.OneHotMask.extend (fun _ : Fin L => 0)=(fun _ : ℕ => 0) := by
  funext i
  simp [_root_.ThreeSum.OneHotMask.extend]

theorem eval_outside {L : ℕ} (Q : Finset (Fin L)) (w : Fin L → ℕ) :
    (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend w) (fun _ => 0) L (_root_.ThreeSum.SubsetAddress.subsetMask Q) : ℤ) =
      ∑ i : Fin L, if i ∈ Q then (0 : ℤ) else (w i : ℤ) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks.extend_zero L,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.eval_subsetMask]
  push_cast
  rfl

theorem eval_difference {h L : ℕ} (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h))
    (Q : Finset (Fin L)) :
    (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,true)).val) (fun _ => 0) L (_root_.ThreeSum.SubsetAddress.subsetMask Q) : ℤ)-
      (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum.OneHotMask.extend fun i => (w (i,false)).val) (fun _ => 0) L (_root_.ThreeSum.SubsetAddress.subsetMask Q) : ℤ)
      = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawOutput w Q := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks.eval_outside,_root_.ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks.eval_outside,← Finset.sum_sub_distrib]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.rawOutput
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : i ∈ Q <;> simp [hi]

theorem mapRow_eq {h : ℕ} (b : Bool) (o : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) :
    _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h b o.val =
      _root_.ThreeSum.OneHotMask.extend (fun i : Fin (464*h) => (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.mapAt h o (i,b)).val) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow,o.isLt,dite_true]

theorem indexed_blockKey {h : ℕ} (o : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h)
    (i : Fin ((464*h).choose (2*h))) :
    (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true o.val) (fun _ => 0) (464*h)
      (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i.val) : ℤ)-
      (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false o.val) (fun _ => 0) (464*h)
      (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i.val) : ℤ) =
      _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey (o,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h i) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks.mapRow_eq,_root_.ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks.mapRow_eq,← _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt i.isLt,_root_.ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks.eval_difference]
  rfl

end ThreeSum.OutputKeyMasks

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact local-output array semantics

The physical occurrence-major rows are the same list of original records
used by the verified global radix product constructor.
-/

namespace ThreeSum.LocalKeyArraySemantics
open _root_.ThreeSum.LocalKeyArraySemantics


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1800000



theorem localKeys_eq_flatMap (h : ℕ) :
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h = (List.finRange (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)).flatMap
      (fun o => List.ofFn (fun i => _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.blockKey (o,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layerRecord h i))) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords,List.product,List.map_flatMap,List.map_map,
    _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.layers,List.map_ofFn,Function.comp_def]

theorem seg_localKeys {h dst : ℕ} {μ : ℕ → ℤ}
    (hout : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ i < _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h,
      μ (dst+j*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h+i)=
        (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true j) (fun _ => 0) (464*h)
          (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i) : ℤ)-
        (_root_.ThreeSum.OneHotMask.eval (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false j) (fun _ => 0) (464*h)
          (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i) : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ dst (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.LocalKeyArraySemantics.localKeys_eq_flatMap]
  apply _root_.ThreeSum1960614.Machine.ThreeSum.LocalKeyArraySemantics.seg_flatMap_rows _ _ (_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) dst (by simp [_root_.ThreeSum.LocalCoverBounds.outputCount])
  intro j hj i hi
  have hj' : j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h := by simpa only [List.length_finRange] using hj
  rw [hout j hj' i hi]
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.OutputKeyMasks.indexed_blockKey ⟨j,hj'⟩ ⟨i,hi⟩
  have ho : (List.finRange (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h))[j]=⟨j,hj'⟩ := by
    apply Fin.ext
    simp
  simpa only [List.getElem_ofFn,ho] using he

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem meets_original {pMain h masks maps dst free : ℕ} {μ : ℕ → ℤ}
    (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*h+3 ≤ lim.depth)
    (hspace : _root_.ThreeSum.LightLocalKeyRow.space free (464*h) (_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) ≤ lim.space)
    (hmasks : masks+_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h ≤ dst)
    (hmaps : maps+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ dst)
    (hdst : dst+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h ≤ free)
    (hword : (_root_.ThreeSum.LightLocalKeys.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h,
      μ (masks+i)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i : ℤ))
    (hreadFalse : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ i < 464*h,
      μ (maps+j*(2*(464*h))+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ i < 464*h,
      μ (maps+j*(2*(464*h))+464*h+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true j i : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [464*h,masks,_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h,maps,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,dst,free] μ
      (_root_.ThreeSum.LightLocalKeys.time (464*h) (_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h))
      (fun _ ν => _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  apply (S.meets (U := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h))
    (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true)
    hw hd hspace hmasks hmaps hdst hword hmaskRead
    (fun i hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_spec hi).1) hreadFalse hreadTrue
    (fun j hj i hi => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_le false hj hi)
    (fun j hj i hi => _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow_le true hj hi)).mono le_rfl
  intro r ν ⟨hout,hkeep⟩
  exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LocalKeyArraySemantics.seg_localKeys hout,hkeep⟩

end ThreeSum.LocalKeyArraySemantics

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# From selected coefficient rows to every original global output key

The fixed program constructs the output-mask layer, all signed local keys,
and the full positional product. Its output is the literal occurrence-aware
`GlobalKeyEnumeration.globalKeys` array. No input key or mask table is assumed.
-/

namespace ThreeSum.LightGlobalKeys
open _root_.ThreeSum.LightGlobalKeys


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 600000
set_option maxRecDepth 10000












section

private theorem private_f3a9b5b6d8_sum_parts (a b c j : ℕ) :
    a ≤ a+b+c+j+464 ∧ b ≤ a+b+c+j+464 ∧
    c ≤ a+b+c+j+464 ∧ j ≤ a+b+c+j+464 := by omega
end


section

private theorem private_4b4b410b3a_word_parts (h J : ℕ) :
    2^(464*h+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J ∧
    _root_.ThreeSum.LightLocalKeys.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J ∧
    _root_.ThreeSum.LightRadixKeys.word (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J ∧
    J ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J :=
  _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.private_f3a9b5b6d8_sum_parts _ _ _ _
end


section

private theorem private_90d95245fd_int_mul_le_word {a b c : ℕ} {w : ℤ}
    (hab : a*b ≤ c) (hc : (c : ℤ) ≤ w) : (a : ℤ)*(b : ℤ) ≤ w := by
  exact (show (a : ℤ)*(b : ℤ) ≤ (c : ℤ) by
    simpa only [Nat.cast_mul] using Int.ofNat_le.mpr hab).trans hc
end


theorem localCount_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h := by
  apply Nat.mul_pos
  · unfold _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize _root_.ThreeSum.LocalHashMoments.scheduleLength
    positivity
  · exact Nat.choose_pos (by omega)

theorem localKeys_length (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h).length=_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localRecords_length,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount]



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}













end ThreeSum.LightGlobalKeys

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
set_option maxHeartbeats 600000
set_option maxRecDepth 10000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs.meets_with_masks__implementation_26be2bb62e {pMain h J maps free : ℕ} {μ : ℕ → ℤ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*h+J+5 ≤ lim.depth)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.space free h J ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J : ℤ) ≤ lim.word)
    (hmaps : maps+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ free)
    (hreadFalse : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ i < 464*h,
      μ (maps+j*(2*(464*h))+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false j i : ℤ))
    (hreadTrue : ∀ j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, ∀ i < 464*h,
      μ (maps+j*(2*(464*h))+464*h+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true j i : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [464*h,2*h,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,J,maps,
      _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h,free] μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.time h J)
      (fun r ν => r=((_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J : ℕ) : ℤ) ∧
        ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J)=((_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.Seg ν (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h+_root_.ThreeSum.LightRadixKeys.offset (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h) J+1) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalKeys h J) ∧
        (∀ i < _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h,
          ν (free+i)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν free) := by
  let n := _root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h
  let m := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount h
  let dst := free+n
  let work := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.scratch free h
  have hwork : work=dst+m := rfl
  have hlspace : _root_.ThreeSum.LightLocalKeyRow.space work (464*h) n ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hgspace : _root_.ThreeSum.LightRadixKeys.space work m J ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hs : work+464*h+2*n+(464*h+1) ≤ lim.space := hlspace
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.word h J) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hpword := hbudget (2^(464*h+1)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.private_4b4b410b3a_word_parts h J).1
  have hlword := hbudget (_root_.ThreeSum.LightLocalKeys.word (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.private_4b4b410b3a_word_parts h J).2.1
  have hgword := hbudget (_root_.ThreeSum.LightRadixKeys.word (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.private_4b4b410b3a_word_parts h J).2.2.1
  have hJword := hbudget J (_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.private_4b4b410b3a_word_parts h J).2.2.2
  have hcount := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount_pos h
  have hlen : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h).length=m := _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localKeys_length h
  have hprodWord : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(n : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*n ≤ lim.space := by change m ≤ lim.space; omega
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.private_90d95245fd_int_mul_le_word hh hw
  have hprodNonneg : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(n : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hprodWord' : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h : ℤ) ≤ lim.word := hprodWord
  have hprodNonneg' : (0 : ℤ) ≤ (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h : ℤ) :=
    mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hproduct : (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h : ℤ)*(_root_.ThreeSum.LocalCoverBounds.outputCount (464*h) h : ℤ)=(m : ℤ) := by
    simp only [m,_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount,Nat.cast_mul]
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.body _root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h * _root_.ThreeSum.LocalCoverBounds.outputCount (464 * h) h : ℕ) ?_ ?_ ?_
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
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (dst : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, dst, n]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [dst, n] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, dst, n] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (work : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hwork, hproduct]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hwork, hproduct] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hwork, hproduct] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.meets (d := d+1) (μ := μ)
    (L := 464*h) (k := 2*h) (dst := free) (work := work)
    S.enum S.powers S.layer hw (by omega) hpword (by omega)
    (by change free+n ≤ work; dsimp [dst] at hwork; omega) (by omega)
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
     on_goal -1 => (rintro count μ₁ ⟨hcountVal, hmasks, hpowers, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hc : count=(n : ℤ) := hcountVal
  have hmRead (i : ℕ) (hi : i < n) : μ₁ (free+i)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i : ℤ) := by
    have hi' : i < (_root_.ThreeSum.SubsetAddress.enumerateLayer (464*h) (2*h)).length := by
      rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]
      exact hi
    have he := hmasks i (by simpa only [List.length_map] using hi')
    simpa only [_root_.ThreeSum.LocalMaskGraph.maskAt,List.getD_eq_getElem _ _ hi',List.getElem_map] using he
  have hfi (j : ℕ) (hj : j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (i : ℕ) (hi : i < 464*h) :
      μ₁ (maps+j*(2*(464*h))+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h false j i : ℤ) := by
    have hh := Nat.mul_le_mul_right (2*(464*h)) (show j+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h by omega)
    simp only [Nat.add_mul,one_mul] at hh
    rw [hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hreadFalse j hj i hi
  have hti (j : ℕ) (hj : j < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (i : ℕ) (hi : i < 464*h) :
      μ₁ (maps+j*(2*(464*h))+464*h+i)=(_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.mapRow h true j i : ℤ) := by
    have hh := Nat.mul_le_mul_right (2*(464*h)) (show j+1 ≤ _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h by omega)
    simp only [Nat.add_mul,one_mul] at hh
    rw [hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hreadTrue j hj i hi
  have hl := _root_.ThreeSum1960614.Machine.ThreeSum.LocalKeyArraySemantics.meets_original (d := d+1) (μ := μ₁)
    (h := h) (masks := free) (maps := maps) (dst := dst) (free := work) S.locals
    hw (by omega) hlspace le_rfl (by dsimp [dst]; omega) (by dsimp [_root_.ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.localCount,m] at *; omega)
    hlword hmRead hfi hti
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hc]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hc] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hc] <;> omega)
     on_goal -1 => (rintro result μ₂ ⟨hkeys, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hg := _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixKeys.meets (src := dst) (dst := work) (p := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
    (U := 464*h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) S.globalProc S.rows S.affine (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys h) hw
    (by rw [hlen]; omega) (by rw [hlen]; exact hcount) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.localKeys_bounded h)
    J (d+1) μ₂ (by simpa only [hlen] using hgspace) hgword (by omega) hkeys
  simp only [hlen] at hg
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hg _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hg ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, m]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [m] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, m] <;> omega)
     on_goal -1 => (rintro final μ₃ ⟨hresult, hheader, hglobal, hkeep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨hresult,hheader,hglobal,?_,?_⟩
  · intro i hi
    change μ₃ (free+i)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) i : ℤ)
    rw [hkeep₃ _ (by dsimp [dst] at hwork; change i < n at hi; omega),
      hkeep₂ _ (by dsimp [dst]; change i < n at hi; omega)]
    exact hmRead i hi
  · intro a ha
    change μ₃ a=μ a
    rw [hkeep₃ _ (by omega),hkeep₂ _ (by dsimp [dst]; omega),
      hkeep₁ _ ⟨by omega,Or.inl ha⟩]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs.meets_with_masks__implementation_26be2bb62e) := (@ThreeSum1960614.Machine.ThreeSum.LightGlobalKeys.Procs.meets_with_masks__implementation_26be2bb62e)

#print axioms solution
