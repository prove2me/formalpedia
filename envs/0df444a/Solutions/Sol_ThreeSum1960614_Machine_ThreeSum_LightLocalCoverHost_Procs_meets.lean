-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:29:59.46673+00:00
-- url     : https://prove2.me/submissions/82609961-d26e-433b-9038-6785c22c8d73

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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightCoverGreedy_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverMatrix_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverSchedule_indices_lt
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverTables_Data_gathered_schedule
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightLocalCoverTables_Data_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightWeightGather_Procs_meets

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.BooleanGreedy
end ThreeSum.BooleanGreedy
namespace ThreeSum.LightLocalCoverHost
end ThreeSum.LightLocalCoverHost
namespace ThreeSum.LightLocalCoverSchedule
end ThreeSum.LightLocalCoverSchedule
namespace ThreeSum.LightLocalCoverTables
end ThreeSum.LightLocalCoverTables
namespace ThreeSum.LightMaskBits
end ThreeSum.LightMaskBits
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalCoverMatrix
end ThreeSum.LocalCoverMatrix
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.MaskErase
end ThreeSum.MaskErase
namespace ThreeSum.OneHotMask
end ThreeSum.OneHotMask
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum.WeightEnumeration
end ThreeSum.WeightEnumeration
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
end ThreeSum1960614.Machine.ThreeSum.BooleanGreedy
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
namespace ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
end ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
namespace ThreeSum1960614.Machine.ThreeSum.LightMaskBits
end ThreeSum1960614.Machine.ThreeSum.LightMaskBits
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
end ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
end ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.MaskErase
end ThreeSum1960614.Machine.ThreeSum.MaskErase
namespace ThreeSum1960614.Machine.ThreeSum.OneHotMask
end ThreeSum1960614.Machine.ThreeSum.OneHotMask
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.WeightEnumeration
end ThreeSum1960614.Machine.ThreeSum.WeightEnumeration

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









end ThreeSum.OneHotMask

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Ordered radix enumeration of local hash coefficients

The Cartesian-product list used by `allWeights` enumerates the first
coordinate most slowly. The radix index consequently stores that coordinate
in its most significant digit. The equality below is equality of lists,
including their order and repetitions, rather than a membership equivalence.
-/

namespace ThreeSum.WeightEnumeration
open _root_.ThreeSum.WeightEnumeration


open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments

variable {ι K : Type*} [DecidableEq ι] [NatCast K]





































theorem decodedWeight_val (L p k : ℕ) (i : Fin L × Bool) :
    (_root_.ThreeSum.WeightEnumeration.decodedWeight (K := ZMod p) L p k i).val = _root_.ThreeSum.WeightEnumeration.digit p (2*L) k (_root_.ThreeSum.WeightEnumeration.coordinateIndex i) := by
  simp [_root_.ThreeSum.WeightEnumeration.decodedWeight,_root_.ThreeSum.WeightEnumeration.digit,ZMod.val_natCast]









end ThreeSum.WeightEnumeration

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

/-! # Boolean-array semantics of the already specified finite greedy schedule -/

namespace ThreeSum.BooleanGreedy
open _root_.ThreeSum.BooleanGreedy


open _root_.Finset
open scoped _root_.BigOperators



























theorem choices_length (matrix : ℕ → ℕ → ℕ) (rows cols t : ℕ) :
    (_root_.ThreeSum.BooleanGreedy.choices matrix rows cols t).length = t := _root_.ThreeSum.Cover.greedyChoices_length ..



end ThreeSum.BooleanGreedy

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits
open _root_.ThreeSum.LightMaskBits


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.MaskErase
open _root_.ThreeSum1960614.Machine.ThreeSum.MaskErase



theorem bit_le (L m j : ℕ) : _root_.ThreeSum.LightMaskBits.bit L m j ≤ 1 := by unfold _root_.ThreeSum.LightMaskBits.bit; split <;> omega













variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}









end ThreeSum.LightMaskBits

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



















end ThreeSum.LocalMaskGraph

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The literal cover-matrix entry is the retained-edge predicate

This identifies the actual all-pairs, histogram-trimmed support table with
the same `Covers` relation used by the finite moment and greedy proof.
-/

namespace ThreeSum.LocalCoverMatrix
open _root_.ThreeSum.LocalCoverMatrix


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes

variable {h L k : ℕ}








theorem entry_le (w : _root_.ThreeSum.LocalHashMoments.Weight L (_root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments.LocalField h)) (k B r : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry w k B r ≤ 1 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry _root_.ThreeSum.LightSupportMark.bit
  split <;> omega













end ThreeSum.LocalCoverMatrix

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact local schedule occurrence indices

The machine's Boolean matrix uses radix-indexed candidate rows and ordered
residue-pair columns. These changes of representation preserve the entire
original local schedule, including ties and repeated selected maps.
-/

namespace ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum.LightLocalCoverSchedule


open _root_.Finset
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding








theorem rows_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h := Nat.pow_pos (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h)











theorem indices_length (h : ℕ) : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length = _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h :=
  _root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.choices_length ..





theorem candidateAt_lt (h : ℕ) (s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h) : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h := by
  have hs : s.val < (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_length]; exact s.isLt
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt
  rw [List.getD_eq_getElem _ _ hs]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_lt h (List.getElem_mem hs)









end ThreeSum.LightLocalCoverSchedule

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables
open _root_.ThreeSum.LightLocalCoverTables


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule





theorem coeff_digit (h j : ℕ) (b : Bool) (i : Fin (464*h)) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff b (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h j) i.val =
      _root_.ThreeSum.WeightEnumeration.digit (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (2*(464*h)) j (2*i.val+(if b then 1 else 0)) := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff,_root_.ThreeSum1960614.Machine.ThreeSum.OneHotMask.extend_fin,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate,
    _root_.ThreeSum1960614.Machine.ThreeSum.WeightEnumeration.decodedWeight_val,_root_.ThreeSum.WeightEnumeration.coordinateIndex]



theorem Data.matrix_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (hr : r < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) :
    μ (matrixPtr+j*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h+r) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.matrix h j r : ℤ) := (H j hj).2.2 r hr









end ThreeSum.LightLocalCoverTables

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule
open _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs.meets__implementation_485f1121c8 {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs P pMain)
    {μ : ℕ → ℤ} {h masks bitPtr maps raw0 raw1 hist0 hist1 matrixPtr work scheduleMaps : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+464*h+6 ≤ lim.depth)
    (hspace : _root_.ThreeSum.LightLocalCoverCandidate.space work (464*h)
      (_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) ≤ lim.space)
    (hmasks : masks+_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h ≤ maps)
    (hbits : bitPtr+_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h*(464*h) ≤ maps)
    (hmaps : maps+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*(2*(464*h)) ≤ raw0)
    (hraw0 : raw0+2*_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h ≤ raw1)
    (hraw1 : raw1+2*_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h ≤ hist0)
    (hhist0 : hist0+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ hist1)
    (hhist1 : hist1+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ matrixPtr)
    (hmatrix : matrixPtr+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h ≤ work)
    (hschedule : work+_root_.ThreeSum.LightCoverGreedy.total (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) ≤ scheduleMaps)
    (houtSpace : scheduleMaps+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h*(2*(464*h)) ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word h : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < _root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h,
      μ (masks+i) = (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) h i : ℤ))
    (hbitsRead : ∀ i < _root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h, ∀ j < 464*h,
      μ (bitPtr+i*(464*h)+j) = (_root_.ThreeSum.LocalCoverMatrix.bits (464*h) h i j : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [464*h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h,_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,
        masks,bitPtr,maps,raw0,raw1,hist0,hist1,matrixPtr,work,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,scheduleMaps]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time h)
      (fun r ν => r = (scheduleMaps : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data ν h maps hist0 hist1 matrixPtr ∧ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows ν h scheduleMaps ∧
        (∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
          ν (_root_.ThreeSum.LightCoverGreedy.out work (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν maps) := by
  have hwork : work ≤ lim.space := by unfold _root_.ThreeSum.LightLocalCoverCandidate.space at hspace; omega
  have hscheduleWork : work ≤ scheduleMaps := by omega
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word h) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hmatrixWord := hbudget
    (_root_.ThreeSum.LightLocalCoverCandidate.word (464*h) (_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h)
      (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word; omega)
  have hgatherWord := hbudget
    (_root_.ThreeSum.LightWeightGather.word (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (2*(464*h))) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word; omega)
  have hLWord := hbudget (464*h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightWeightGather.word; omega)
  have hWWord := hbudget (2*(464*h)) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightWeightGather.word; omega)
  have hWWordZ : (2 : ℤ)*(464*(h : ℤ)) ≤ lim.word := by exact_mod_cast hWWord
  have h2Word := hbudget 2 (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word
    omega)
  have hpWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word
    omega)
  have hp2Word := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word
    omega)
  have hp2WordZ : (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℤ)*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ lim.word := by exact_mod_cast hp2Word
  have hNWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightWeightGather.word; omega)
  have hTWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightWeightGather.word; omega)
  have hnWord := hbudget (_root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word
    omega)
  have hcapWord := hbudget (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h) (by
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.word _root_.ThreeSum.LightLocalCoverCandidate.word _root_.ThreeSum.LightPairFlags.word
    omega)
  have hn : 0 < _root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h := Nat.choose_pos (by omega)
  have hmapsWork : maps+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*(2*(464*h)) ≤ work := by omega
  have hhist0Work : hist0+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ work := by omega
  have hhist1Work : hist1+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ work := by omega
  have hgreedySpace : work+_root_.ThreeSum.LightCoverGreedy.total (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) ≤ lim.space := by omega
  have houtEnd : _root_.ThreeSum.LightCoverGreedy.out work (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ scheduleMaps := by
    unfold _root_.ThreeSum.LightCoverGreedy.out _root_.ThreeSum.LightCoverGreedy.total at *
    omega
  have hm := S.matrix.meets (d := d+1) (μ := μ) (L := 464*h)
    (n := _root_.ThreeSum.LocalMaskGraph.vertexCount (464*h) h) (p := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h) (cap := _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h)
    (N := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (masks := masks) (bitPtr := bitPtr) (maps := maps) (raw0 := raw0)
    (raw1 := raw1) (hist0 := hist0) (hist1 := hist1) (dst := matrixPtr) (work := work)
    (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) h) (_root_.ThreeSum.LocalCoverMatrix.bits (464*h) h)
    (fun j => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff false (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h j))
    (fun j => _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskHashes.coeff true (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidate h j))
    hw (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime_pos h) hn hspace hmasks hbits hmaps hraw0 hraw1 hhist0 hhist1
    hmatrix hmatrixWord hmaskRead (fun _ hi => (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_spec hi).1) hbitsRead
    (fun i _ j _ => _root_.ThreeSum1960614.Machine.ThreeSum.LightMaskBits.bit_le (464*h) (_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) h i) j)
    (by intro j _ i hi; simpa only [Bool.false_eq_true,ite_false,Nat.add_zero] using _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.coeff_digit h j false ⟨i,hi⟩)
    (by intro j _ i hi; simpa only [ite_true] using _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.coeff_digit h j true ⟨i,hi⟩)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body S.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.body _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hm _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hm ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;> omega)
     on_goal -1 => (rintro vm μ₁ ⟨hdata₁, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have H₁ : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ₁ h maps hist0 hist1 matrixPtr := hdata₁
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h * _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hg := S.greedy.meets (d := d+1) (μ := μ₁) (src := matrixPtr) (activePtr := work)
    (rows := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (cols := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h) (rounds := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.matrix h)
    hw (by omega) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows_pos h) hmatrix hgreedySpace
    (fun _ hi _ hr => H₁.matrix_read hi hr) (fun _ _ _ _ => _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverMatrix.entry_le ..) (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;> omega)
     on_goal -1 => (rintro vg μ₂ ⟨hvg, hchoices, hactive, hkeep₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have H₂ : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ₂ h maps hist0 hist1 matrixPtr :=
    H₁.of_kept (fun a ha => hkeep₂ a (Or.inl ha)) hmapsWork hhist0Work hhist1Work hmatrix
  have hselection : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,
      μ₂ (_root_.ThreeSum.LightCoverGreedy.out work (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)+s) = ((_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).getD s 0 : ℤ) := by
    intro s hs
    have hs' : s < (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).length := by rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices_length]; exact hs
    have hr := hchoices s (by simpa only [List.length_map,_root_.ThreeSum1960614.Machine.ThreeSum.BooleanGreedy.choices_length] using hs)
    rw [List.getD_eq_getElem _ _ hs']
    simpa only [List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices] using hr
  have hselectionLt : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h, (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).getD s 0 < _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h := by
    intro s hs
    exact _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt_lt h ⟨s,hs⟩
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (2 * (464 * h) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hc := S.gather.meets (d := d+1) (μ := μ₂)
    (indices := _root_.ThreeSum.LightCoverGreedy.out work (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)) (src := maps) (dst := scheduleMaps)
    (N := _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (rows := _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (width := 2*(464*h)) (fun s => (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.indices h).getD s 0)
    hw (by omega) houtEnd (by omega) houtSpace hgatherWord hselectionLt hselection
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hc _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hc ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time, hvg, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time, hvg, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time, hvg, _root_.ThreeSum.LightCoverGreedy.out, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols] <;> omega)
     on_goal -1 => (rintro vc μ₃ ⟨hcopy, hkeep₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have H₃ : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.Data μ₃ h maps hist0 hist1 matrixPtr :=
    H₂.of_kept (fun a ha => hkeep₃ a (Or.inl (by omega))) hmapsWork hhist0Work hhist1Work hmatrix
  have hrows₃ : _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverTables.ScheduleRows μ₃ h scheduleMaps := H₂.gathered_schedule hcopy
  have hselection₃ : ∀ s : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.Occurrence h,
      μ₃ (_root_.ThreeSum.LightCoverGreedy.out work (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h) (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.cols h)+s.val) = (_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.candidateAt h s : ℤ) := by
    intro s
    rw [hkeep₃ _ (Or.inl (by have hs := s.isLt; omega))]
    exact hselection s.val s.isLt
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (scheduleMaps : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.time] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨rfl,H₃,hrows₃,hselection₃,?_⟩
  intro a ha
  change μ₃ a = μ a
  rw [hkeep₃ a (Or.inl (by omega)),hkeep₂ a (Or.inl (by omega))]
  exact hkeep₁ a ha
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs.meets__implementation_485f1121c8) := (@ThreeSum1960614.Machine.ThreeSum.LightLocalCoverHost.Procs.meets__implementation_485f1121c8)

#print axioms solution
