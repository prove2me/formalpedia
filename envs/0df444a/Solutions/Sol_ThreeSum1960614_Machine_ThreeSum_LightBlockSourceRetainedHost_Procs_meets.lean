-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:35:14.730813+00:00
-- url     : https://prove2.me/submissions/97015516-4f50-4f85-80ef-05ae3b4138b4

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle016
import Definitions.Def_ThreeSum1960614_Machine_Bundle017
import Definitions.Def_ThreeSum1960614_Machine_Bundle018
import Definitions.Def_ThreeSum1960614_Machine_Bundle019
import Definitions.Def_ThreeSum1960614_Machine_Bundle020
import Definitions.Def_ThreeSum1960614_Machine_Bundle021
import Definitions.Def_ThreeSum1960614_Machine_Bundle022
import Definitions.Def_ThreeSum1960614_Machine_Bundle023
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
import Mathlib.Algebra.Order.Ring.Nat
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
import Mathlib.Data.List.Range
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
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockSourceCoverInput_Input_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourcePreparation_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceRetainedStages_meets_left
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceRetainedStages_meets_right
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightDownsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_SubsetAddress_layerRank_lt

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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.BlockSourceFlags
end ThreeSum.BlockSourceFlags
namespace ThreeSum.BlockSourceTableLayout
end ThreeSum.BlockSourceTableLayout
namespace ThreeSum.LightBlockSourceRetainedHost
end ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.SourceTableLayout
end ThreeSum.SourceTableLayout
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
end ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout
end ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.SourceTableLayout
end ThreeSum1960614.Machine.ThreeSum.SourceTableLayout
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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















































@[simp] theorem layerOffset_zero (L : ℕ) : _root_.ThreeSum.SubsetAddress.layerOffset L 0 = 0 := by
  simp [_root_.ThreeSum.SubsetAddress.layerOffset]

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









theorem enumerateThrough_length (L k : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateThrough L k).length = _root_.ThreeSum.SubsetAddress.layerOffset L (k + 1) := by
  induction k with
  | zero => simp [_root_.ThreeSum.SubsetAddress.enumerateThrough, _root_.ThreeSum.SubsetAddress.enumerateLayer_length, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ]
  | succ k ih =>
      rw [_root_.ThreeSum.SubsetAddress.enumerateThrough, List.length_append, ih, _root_.ThreeSum.SubsetAddress.enumerateLayer_length,
        _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.layerOffset_succ L (k + 1)]

theorem enumerateDownset_length (L cut : ℕ) :
    (_root_.ThreeSum.SubsetAddress.enumerateDownset L cut).length = _root_.ThreeSum.SubsetAddress.downsetCap L cut :=
  _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateThrough_length L (min cut L)

theorem mem_enumerateThrough (L k m : ℕ) :
    m ∈ _root_.ThreeSum.SubsetAddress.enumerateThrough L k ↔ m < 2 ^ L ∧ _root_.ThreeSum.SubsetAddress.weight L m ≤ k := by
  induction k with
  | zero => simp [_root_.ThreeSum.SubsetAddress.enumerateThrough, _root_.ThreeSum.SubsetAddress.mem_enumerateLayer, _root_.ThreeSum.SubsetAddress.IsMask]
  | succ k ih =>
      simp only [_root_.ThreeSum.SubsetAddress.enumerateThrough, List.mem_append, ih, _root_.ThreeSum.SubsetAddress.mem_enumerateLayer, _root_.ThreeSum.SubsetAddress.IsMask]
      omega

theorem mem_enumerateDownset (L cut m : ℕ) :
    m ∈ _root_.ThreeSum.SubsetAddress.enumerateDownset L cut ↔ m < 2 ^ L ∧ _root_.ThreeSum.SubsetAddress.weight L m ≤ cut := by
  rw [_root_.ThreeSum.SubsetAddress.enumerateDownset, _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateThrough]
  constructor
  · rintro ⟨hm, hk⟩
    exact ⟨hm, hk.trans (min_le_left _ _)⟩
  · rintro ⟨hm, hk⟩
    exact ⟨hm, le_min hk (_root_.ThreeSum.SubsetAddress.weight_le_width hm)⟩





































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















@[simp] theorem index_unindex {J L : ℕ} (S : Finset (Fin (J*L))) :
    _root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum.BlockIndex.unindexSet (J := J) (L := L) S) = S := by
  ext c
  simp [_root_.ThreeSum.BlockIndex.unindexSet,_root_.ThreeSum.BlockIndex.indexSet]



















end ThreeSum.BlockIndex

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual compact enumeration uses the actual compact table addresses

This bridges a sequentially constructed source array to `TableAt`: the mask
stored at `subsetRank S` by the existing enumerator is exactly `subsetMask S`.
No additional scatter, rank oracle, or arbitrary enumeration is required.
-/

namespace ThreeSum.SourceTableLayout
open _root_.ThreeSum.SourceTableLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress

set_option maxHeartbeats 800000

















theorem maskAt_mem {L cut i : ℕ} (hi : i < _root_.ThreeSum.SubsetAddress.downsetCap L cut) :
    _root_.ThreeSum.SourceTableLayout.maskAt L cut i ∈ _root_.ThreeSum.SubsetAddress.enumerateDownset L cut := by
  unfold _root_.ThreeSum.SourceTableLayout.maskAt
  rw [List.getD_eq_getElem _ _ (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateDownset_length] using hi)]
  exact List.getElem_mem _

theorem maskAt_lt {L cut i : ℕ} (hi : i < _root_.ThreeSum.SubsetAddress.downsetCap L cut) :
    _root_.ThreeSum.SourceTableLayout.maskAt L cut i < 2^L :=
  ((_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.mem_enumerateDownset L cut _).mp (_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.maskAt_mem hi)).1



theorem subsetMask_setAt {L cut i : ℕ} (hi : i < _root_.ThreeSum.SubsetAddress.downsetCap L cut) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.SourceTableLayout.setAt L cut i) = _root_.ThreeSum.SourceTableLayout.maskAt L cut i :=
  _root_.ThreeSum.MaskDecode.subsetMask_decode (_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.maskAt_lt hi)







end ThreeSum.SourceTableLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.BlockSourceEncoding


open _root_.Finset
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LightSourceResidues
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
open scoped _root_.BigOperators

set_option maxHeartbeats 1000000











@[simp] theorem modulus_cast (h J : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J : ℤ) = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus h J := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]





end OriginalSources

end ThreeSum.BlockSourceEncoding

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Compact source arrays in the unchanged block-query coordinate system -/

namespace ThreeSum.BlockSourceTableLayout
open _root_.ThreeSum.BlockSourceTableLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockRows
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding



theorem mask_sets {h J cut i : ℕ} (hi : i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i)) = _root_.ThreeSum.SourceTableLayout.maskAt (J*(464*h)) cut i := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets,_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex.index_unindex,_root_.ThreeSum1960614.Machine.ThreeSum.SourceTableLayout.subsetMask_setAt hi]







end ThreeSum.BlockSourceTableLayout

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.BlockIndex
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockIndex
open _root_.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild
set_option maxHeartbeats 4000000
set_option maxRecDepth 14000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs.meets__implementation_7400d5fcf4 {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      masks coeff0 coeff1 rawLeft rawRight flags baseL baseR maskBase bitBase rowOut work : ℕ}
    {shift : ℤ} (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+9 ≤ lim.depth)
    (hcut : cut ≤ J*(464*h))
    (hocc : occ+J ≤ masks) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ masks)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ masks)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ masks)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ masks)
    (hsourceHistL : sourceHistL+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ masks)
    (hsourceHistR : sourceHistR+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ masks)
    (hmasks : masks+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ coeff0)
    (hc0 : coeff0+J*(464*h) ≤ coeff1) (hc1 : coeff1+J*(464*h) ≤ rawLeft)
    (hrawLeft : rawLeft+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ rawRight)
    (hrawRight : rawRight+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ flags)
    (hflags : flags+2*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+2 ≤ baseL)
    (hbaseL : baseL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ baseR)
    (hbaseR : baseR+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ maskBase)
    (hmaskBase : maskBase+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut ≤ bitBase)
    (hbits : bitBase+J*(464*h) ≤ rowOut) (hrowOut : rowOut+2 ≤ work)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space work h J ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ i : Fin NL, vL i.val = b (eL i))
    (hinputR : ∀ i : Fin NR, vR i.val = a (eR i))
    (hhistReadL : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistL+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistR+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ j < J, μ (occ+j) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,masks,coeff0,coeff1,rawLeft,rawRight,flags,
        baseL,baseR,maskBase,bitBase,rowOut,work]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.time h J cut) (fun _ ν =>
        _root_.ThreeSum.LightZetaStages.StoredThrough ν baseL cut (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(464*h)) ∧
        _root_.ThreeSum.LightZetaStages.StoredThrough ν baseR cut (_root_.ThreeSum1960614.Machine.ThreeSum.BlockIndexedQuery.rightSource (p : ℤ) shift A a q) (J*(464*h)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν masks) := by
  have hsEnum : work+(J*(464*h)+1) ≤ lim.space := (le_max_left _ _).trans hspace
  have hsRest := (le_max_right _ _).trans hspace
  have hsPrep : _root_.ThreeSum.LightSourcePreparation.space work J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ lim.space :=
    (le_max_left _ _).trans hsRest
  have hsStages : _root_.ThreeSum.LightSourceRetainedStages.space work (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) ≤ lim.space :=
    (le_max_right _ _).trans hsRest
  have hwEnum : ((2^(J*(464*h)+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(J*(464*h)+1) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J :=
      (Nat.le_add_right _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwPrep : (_root_.ThreeSum.LightSourcePreparation.word J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
      ((464*h).choose h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightSourcePreparation.word J (464*h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h)
        ((464*h).choose h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J :=
      (Nat.le_add_left _ _).trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwLeft : (_root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) NL : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) NL ≤
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J := (Nat.le_add_left _ _).trans (Nat.le_add_right _ _)
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwRight : (_root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) NR : ℤ) ≤ lim.word := by
    have hh : _root_.ThreeSum.LightSourceRetainedStages.word (J*(464*h)) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBuild.endpointBound h J) NR ≤
        _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J := Nat.le_add_left _ _
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(464*(h : ℤ)) ≤ lim.word := by
    exact (by exact_mod_cast (show J*(464*h) ≤ lim.space by omega) :
      (J : ℤ)*(464*(h : ℤ)) ≤ lim.space).trans hw
  have hwidthNonneg : (0 : ℤ) ≤ (J : ℤ)*(464*(h : ℤ)) := by positivity
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.body _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.time
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightDownsetEnumerationSetup.meets (d := d+1) (μ := μ) (L := J*(464*h))
    (cut := cut) (dst := masks) (work := work) C.enumMain C.powers C.downset C.layer
    hw hsEnum hwEnum hcut (by omega) (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;> omega)
     on_goal -1 => (rintro count ν₁ ⟨hcount, hseg, _, kept₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst count
  have keptEnum : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₁ masks := by
    intro x hx
    exact kept₁ x ⟨by omega,Or.inl hx⟩
  have hcover' := hcover.of_kept keptEnum hmaps hcandidates hleft hright
  have hocc' : ∀ j < J, ν₁ (occ+j) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) j : ℤ) := by
    intro j hj
    exact (keptEnum _ (by omega)).trans (hoccRead j hj)
  have hmaskRead : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,
      ν₁ (masks+i) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.BlockIndex.indexSet (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i)) : ℤ) := by
    intro i hi
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.mask_sets hi,_root_.ThreeSum.SourceTableLayout.maskAt,
      List.getD_eq_getElem _ _ (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateDownset_length] using hi)]
    exact hseg.getElem (by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.enumerateDownset_length] using hi)
  have hpRun := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourcePreparation.meets (d := d+1) (μ := ν₁) C.prepare
    (occ := occ) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
    (masks := masks) (n := _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) (coeff0 := coeff0) (coeff1 := coeff1)
    (rawLeft := rawLeft) (rawRight := rawRight) (flags := flags) (bitBase := bitBase)
    (rowOut := rowOut) (work := work) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut)
    hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) hmasks hc0 hc1
    hrawLeft hrawRight (by omega) hbits hrowOut hsPrep hwPrep hocc'
    hcover'.candidates hcover'.leftRows hcover'.rightRows hcover'.leftCounts hcover'.rightCounts hmaskRead
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hpRun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hpRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;> omega)
     on_goal -1 => (rintro r ν₂ ⟨rawL, rawR, flagL, flagR, kept₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have keptPrep : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₂ masks := by
    intro x hx
    exact (kept₂ x (by omega)).trans (keptEnum x hx)
  have hhL : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      ν₂ (sourceHistL+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 vL NL r : ℤ) := by
    intro r hr
    exact (keptPrep _ (by omega)).trans (hhistReadL r hr)
  have hlRun := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_left (d := d+1) (μ := ν₂) C.stages
    (N := NL) (raw := rawLeft) (flags := flags) (p := p) (table := sourceHistL)
    (base := baseL) (work := work) (cut := cut) (maskBase := maskBase)
    B b q vL eL hw (by omega) hcut (by omega) (by omega) (by omega) (by omega)
    (by omega) hsStages hwLeft hinputL hhL rawL flagL
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hlRun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hlRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;> omega)
     on_goal -1 => (rintro r ν₃ ⟨storedL, kept₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have keptLeft : _root_.ThreeSum1960614.Machine.Light.Kept μ ν₃ masks := by
    intro x hx
    exact (kept₃ x (by omega)).trans (keptPrep x hx)
  have hhR : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      ν₃ (sourceHistR+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift vR NR r : ℤ) := by
    intro r hr
    exact (keptLeft _ (by omega)).trans (hhistReadR r hr)
  have rawR' : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,
      ν₃ (rawRight+i) = _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.endpointRight (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i) := by
    intro i hi
    exact (kept₃ _ (by omega)).trans (rawR i hi)
  have flagR' : ∀ i < _root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,
      ν₃ (flags+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+i) =
        (if _root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.RightAllowed (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences q) (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceTableLayout.sets h J cut i) then 1 else 0 : ℕ) := by
    intro i hi
    exact (kept₃ _ (by omega)).trans (flagR i hi)
  have hrRun := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedStages.meets_right (d := d+1) (μ := ν₃) C.stages
    (N := NR) (raw := rawRight) (flags := flags+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) (p := p)
    (table := sourceHistR) (base := baseR) (work := work) (cut := cut) (maskBase := maskBase)
    A a q vR eR hw (by omega) hcut (by omega) (by omega) (by omega) hbaseR
    (by omega) hsStages hwRight hinputR hhR rawR' flagR'
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrRun _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrRun ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightDownsetEnumerationSetup.time, _root_.ThreeSum.LightDownsetEnumeration.time, _root_.ThreeSum.LightSourcePreparation.time, _root_.ThreeSum.LightSourceRetainedStages.time] <;> omega)
     on_goal -1 => (rintro r ν₄ ⟨storedR, kept₄⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine ⟨?_,storedR,?_⟩
  · intro j hj S hS
    have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
    have hmul := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) (Nat.succ_le_succ hj)
    have haddr : _root_.ThreeSum.LightZetaStages.stageBase baseL (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S < baseR := by
      calc
        _root_.ThreeSum.LightZetaStages.stageBase baseL (_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S
            < baseL+j*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut+_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut :=
          Nat.add_lt_add_left hr _
        _ = baseL+(j+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut := by ring
        _ ≤ baseL+(J*(464*h)+1)*_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut := Nat.add_le_add_left hmul _
        _ ≤ baseR := hbaseL
    exact (kept₄ _ haddr).trans (storedL j hj S hS)
  · intro x hx
    exact (kept₄ x (by omega)).trans (keptLeft x hx)
end

end

theorem solution.{u_implementation_0,u_implementation_1} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs.meets__implementation_7400d5fcf4.{u_implementation_0,u_implementation_1}) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.Procs.meets__implementation_7400d5fcf4.{u_implementation_0,u_implementation_1})

#print axioms solution
