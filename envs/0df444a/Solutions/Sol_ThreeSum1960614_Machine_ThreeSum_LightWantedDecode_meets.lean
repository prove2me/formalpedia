-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:33:54.904497+00:00
-- url     : https://prove2.me/submissions/5e4a7f74-4ba2-43d1-8542-ff12b25ad5ab

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
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle001
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
import Definitions.Def_ThreeSum1962Source_Bundle14
import Definitions.Def_ThreeSum1962Source_Bundle15
import Lean
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Colex
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.Embedding
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
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
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Range
import Mathlib.Data.List.TakeDrop
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecodeDivide_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightOutputDecode_Procs_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_OutputDecodeRecords_global_record_block
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_OutputDecodeRecords_localRecords_getD

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Emod
end Light.Emod
namespace ThreeSum
end ThreeSum
namespace ThreeSum.GlobalKeyEnumeration
end ThreeSum.GlobalKeyEnumeration
namespace ThreeSum.LightOutputDecodeDivide
end ThreeSum.LightOutputDecodeDivide
namespace ThreeSum.LightOutputDecodeOriginal
end ThreeSum.LightOutputDecodeOriginal
namespace ThreeSum.LightWantedDecode
end ThreeSum.LightWantedDecode
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
namespace ThreeSum.LocalHashMoments
end ThreeSum.LocalHashMoments
namespace ThreeSum.LocalMaskGraph
end ThreeSum.LocalMaskGraph
namespace ThreeSum.MaskDecode
end ThreeSum.MaskDecode
namespace ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum.OutputDecodeOrder
end ThreeSum.OutputDecodeOrder
namespace ThreeSum.OutputDecodeRecords
end ThreeSum.OutputDecodeRecords
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Emod
end ThreeSum1960614.Machine.Light.Emod
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
end ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide
namespace ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal
end ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal
namespace ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
end ThreeSum1960614.Machine.ThreeSum.LightWantedDecode
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
namespace ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
end ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
namespace ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
end ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph
namespace ThreeSum1960614.Machine.ThreeSum.MaskDecode
end ThreeSum1960614.Machine.ThreeSum.MaskDecode
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
namespace ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
end ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

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

/-- A specification holds with every larger bound on the time. -/
theorem Meets.mono_time (h : _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T R) (hT : T ≤ T' := by omega) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d vals μ T' R :=
  h.mono hT fun _ _ hR => hR





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
# The remainder of a division

emod(x, M, fr) returns the remainder of the integer x modulo M ≥ 1, a number in 0, …, M - 1.  The
language has no division: the routine writes M, 2M, 4M, … into a table at the free pointer fr as
long as they are at most |x|, subtracts them from |x| from the largest down where possible, and
corrects the sign (`emod_meets`).  With k = `emodRounds |x| M` doublings it takes `emodTime |x| M`
steps, a constant times k + 1, and k cells.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
namespace Emod
open _root_.Light.Emod









end Emod



















/-- There are at most log₂ (V + 1) + 1 doublings for a number up to V. -/
theorem emodRounds_le {a M V : ℕ} (ha : a ≤ V) : _root_.Light.emodRounds a M ≤ Nat.log 2 (V + 1) + 1 := by
  rw [_root_.Light.emodRounds, Nat.size_le]
  calc a / M ≤ a := Nat.div_le_self _ _
    _ < V + 1 := by omega
    _ < 2 ^ (Nat.log 2 (V + 1) + 1) := Nat.lt_pow_succ_log_self (by norm_num) _


namespace Emod
open _root_.Light.Emod






variable {μ : ℕ → ℤ} {x : ℤ} {Mo V fr a : ℕ}









end Emod

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Binary quotient for physical output indices

The existing checked doubling table is reused. During descending
subtraction this routine also accumulates the quotient bits, so its time
is logarithmic in the numerator rather than linear in the quotient.
-/

namespace ThreeSum.LightOutputDecodeDivide
open _root_.ThreeSum.LightOutputDecodeDivide


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Light.Emod
open _root_.ThreeSum1960614.Machine.Light.Emod

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000












variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ ν : ℕ → ℤ} {a Mo V fr : ℕ}





theorem time_le_budget {a Mo V : ℕ} (ha : a ≤ V) : _root_.ThreeSum.LightOutputDecodeDivide.time a Mo ≤ _root_.ThreeSum.LightOutputDecodeDivide.budget V := by
  have hh := _root_.ThreeSum1960614.Machine.Light.emodRounds_le ha (M := Mo)
  unfold _root_.ThreeSum.LightOutputDecodeDivide.time _root_.ThreeSum.LightOutputDecodeDivide.budget
  omega

theorem bounded_meets {pMain : ℕ} (hmain : P[pMain]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.body)
    (F : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim Mo V fr) (haV : a ≤ V) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [a,Mo,fr] μ (_root_.ThreeSum.LightOutputDecodeDivide.budget V)
      (fun q ν => q = ((a/Mo : ℕ) : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν fr) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.meets hmain F haV).mono_time (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.time_le_budget haV)





end ThreeSum.LightOutputDecodeDivide

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A physical global-record index decodes to the original occurrence and mask rows -/

namespace ThreeSum.OutputDecodeRecords
open _root_.ThreeSum.OutputDecodeRecords


open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration
open _root_.ThreeSum.LocalHashMoments
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalHashMoments
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000







theorem localCount_pos (h : ℕ) : 0 < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h := Nat.mul_pos (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)











theorem localIndex_lt {h J k j : ℕ} (hj : j < J) : _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localIndex h J k j < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h :=
  _root_.ThreeSum.OutputDecodeOrder.indices_getD_lt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount_pos h) hj



theorem maskIndex_lt (h J k j : ℕ) : _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.maskIndex h J k j < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h :=
  Nat.mod_lt _ (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h)









theorem original_occurrence_index {h J k : ℕ} (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (j : Fin J) :
    (((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) j).1.val = _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.occurrenceIndex h J k j.val := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.global_record_block hk j,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localRecords_getD (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localIndex_lt j.isLt)]
  rfl

theorem original_output_mask {h J k : ℕ} (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (j : Fin J) :
    _root_.ThreeSum.SubsetAddress.subsetMask ((((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalKeyEnumeration.globalRecords h J).getD k (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.outputDefault h J)) j).2.val) =
      _root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.maskIndex h J k j.val) := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.global_record_block hk j,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localRecords_getD (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localIndex_lt j.isLt)]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.subsetMask_setAt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.maskIndex_lt h J k j.val)





end ThreeSum.OutputDecodeRecords

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Occurrence-only source-bank indices, with first block most significant -/

namespace ThreeSum.OutputDecodeOccurrenceCode
open _root_.ThreeSum.OutputDecodeOccurrenceCode


open _root_.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOrder
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding

set_option maxHeartbeats 1500000



theorem last_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (k : ℕ) :
    (k%(T*M))/M < T :=
  (Nat.div_lt_iff_lt_mul hM).mpr (Nat.mod_lt _ (Nat.mul_pos hT hM))

theorem code_lt {T M : ℕ} (hT : 0 < T) (hM : 0 < M) (J k : ℕ) : _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J k < T^J := by
  induction J generalizing k with
  | zero => simp [_root_.ThreeSum.OutputDecodeOccurrenceCode.code]
  | succ J ih =>
    have hm := Nat.mul_le_mul_left T (show _root_.ThreeSum.OutputDecodeOccurrenceCode.code T M J (k/(T*M))+1 ≤ T^J by exact ih _)
    have hd := _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.last_lt hT hM k
    simp only [Nat.mul_add,Nat.mul_one] at hm
    rw [_root_.ThreeSum.OutputDecodeOccurrenceCode.code,pow_succ']
    omega









end ThreeSum.OutputDecodeOccurrenceCode

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# The actual decoder specializes to the original global output record

The physical right-hand key index selects exactly the unchanged original
record, even when several records have equal key values. This module
identifies the two constructed rows with that record's original schedule
occurrences and Q masks, and exposes the source occurrence array directly.
-/

namespace ThreeSum.LightOutputDecodeOriginal
open _root_.ThreeSum.LightOutputDecodeOriginal


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 1200000









theorem mask_bound (h : ℕ) {s : ℕ} (hs : s < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) :
    _root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) s ≤ 2^(464*h) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LocalMaskGraph.maskAt_spec hs).1.le

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {h J k masks dst work V : ℕ}

theorem meets {pMain : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hk : k < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J) (hkV : k ≤ V)
    (hmask : masks+_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h ≤ dst) (hsep : dst+J+J ≤ work)
    (hspace : _root_.ThreeSum.LightOutputDecode.space work V ≤ lim.space)
    (hword : (_root_.ThreeSum.LightOutputDecode.word V (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J (2^(464*h)) : ℤ) ≤ lim.word)
    (hread : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,
      μ (masks+s)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) s : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [k,J,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,masks,dst,work] μ
      (_root_.ThreeSum.LightOutputDecode.time J V)
      (fun r ν =>
        r=(_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J k : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.Rows ν dst h J k ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  refine (S.meets hw hd (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h) hkV hmask hsep
    hspace hword (fun s hs => _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.mask_bound h hs) hread).mono le_rfl ?_
  rintro r ν ⟨hr,hocc,hmasks,hkeep⟩
  refine ⟨hr,⟨?_,?_⟩,hkeep⟩
  · intro j
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.original_occurrence_index hk j]
    exact hocc j.val j.isLt
  · intro j
    rw [_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.original_output_mask hk j]
    exact hmasks j.val j.isLt



end ThreeSum.LightOutputDecodeOriginal

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Decode an actual emitted wanted-pair cell

The host loads the two physical indices, splits the left index into its
incidence position and lift, and decodes the right index into the original
occurrence and Q-mask rows. Its four-cell header retains both source labels
and the occurrence-only bank index. Division is the verified binary routine.
-/

namespace ThreeSum.LightWantedDecode
open _root_.ThreeSum.LightWantedDecode


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000









theorem decoder_power_bound (V T M J U N : ℕ) :
    T^J ≤ _root_.ThreeSum.LightOutputDecode.word V T M J U+4*V+4*N+32 := by
  unfold _root_.ThreeSum.LightOutputDecode.word
  omega



variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}











end ThreeSum.LightWantedDecode

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightWantedDecode
open _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
open _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords
set_option maxHeartbeats 1800000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ}
    {pairs slot N h J masks dst work i j V : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.meets__implementation_291166e7b2 {pMain pDecode : ℕ} (S : _root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecode.Procs P pDecode)
    (hmain : P[pMain]?=some (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.body S.pDivide pDecode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+3 < lim.depth)
    (hN : 0 < N) (hi : i ≤ V) (hj : j ≤ V) (hkey : j < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.localCount h^J)
    (hpairs : pairs+2*slot+2 ≤ dst)
    (hmask : masks+_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h ≤ dst) (hsep : dst+4+J+J ≤ work)
    (hspace : _root_.ThreeSum.LightWantedDecode.space work V ≤ lim.space) (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word V N h J : ℤ) ≤ lim.word)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,
      μ (masks+s)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) s : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [pairs,slot,N,J,_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h,_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,masks,dst,work] μ (_root_.ThreeSum.LightWantedDecode.time J V)
      (fun r ν =>
        r=(_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℤ) ∧
        _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.Stored ν dst N h J i j ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst) := by
  have hbudget (a : ℕ) (ha : a ≤ _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word V N h J) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hVWord := hbudget V (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word; omega)
  have hiWord : (i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hi).trans hVWord
  have hjWord : (j : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hj).trans hVWord
  have hNWord := hbudget N (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word; omega)
  have hwork : work ≤ lim.space := by unfold _root_.ThreeSum.LightWantedDecode.space _root_.ThreeSum.LightOutputDecode.space at hspace; omega
  have hdecodeWord := hbudget
    (_root_.ThreeSum.LightOutputDecode.word V (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J (2^(464*h)))
    (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word; omega)
  have hfr : _root_.ThreeSum1960614.Machine.Light.Emod.Pre lim N V work := by
    refine ⟨hN,hw,?_,hspace⟩
    have hh := hbudget (4*V+4*N+16) (by unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.word; omega)
    exact_mod_cast hh
  let q := i/N
  let s := i%N
  have hqV : q ≤ V := (Nat.div_le_self _ _).trans hi
  have hsV : s ≤ V := (Nat.mod_le _ _).trans hi
  have hqWord : (q : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hqV).trans hVWord
  have hsWord : (s : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hsV).trans hVWord
  have hprod : q*N ≤ V := (Nat.div_mul_le_self _ _).trans hi
  have hprodWord : (q : ℤ)*(N : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprod : (q : ℤ)*(N : ℤ) ≤ (V : ℤ)).trans hVWord
  have hprodNonneg : (0 : ℤ) ≤ (q : ℤ)*(N : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hdiff : (i : ℤ)-(q : ℤ)*(N : ℤ)=(s : ℤ) := by
    have hh : (N : ℤ)*(q : ℤ)+(s : ℤ)=(i : ℤ) := by
      exact_mod_cast Nat.div_add_mod i N
    nlinarith
  have hbank : _root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j ≤
      (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)^J :=
    (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeOccurrenceCode.code_lt (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.schedule_pos h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount_pos h) J j).le
  have hpowerWord := hbudget ((_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h)^J)
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.decoder_power_bound V (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J (2^(464*h)) N)
  have hbankWord : (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hbank).trans hpowerWord
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.body _root_.ThreeSum.LightWantedDecode.time
  have hleftAddr : ((pairs : ℤ)+2*(slot : ℤ)).toNat=pairs+2*slot := by omega
  have hrightAddr : ((pairs : ℤ)+2*(slot : ℤ)+1).toNat=pairs+2*slot+1 := by omega
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (i : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hleft, hleftAddr]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hleft, hleftAddr] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hleft, hleftAddr] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (j : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hright, hrightAddr]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hright, hrightAddr] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hright, hrightAddr] <;> omega)
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
     first
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.bounded_meets (d := d + 1) S.divide hfr hi) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeDivide.bounded_meets (d := d + 1) S.divide hfr hi) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro quotient μ₁ ⟨hquot, hkeep₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hquot' : quotient=(q : ℤ) := hquot
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (s : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hquot', hdiff]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hquot', hdiff] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hquot', hdiff] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  have hread₁ : ∀ t < _root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h,
      μ₁ (masks+t)=(_root_.ThreeSum.LocalMaskGraph.maskAt (464*h) (2*h) t : ℤ) := by
    intro t ht
    rw [hkeep₁ _ (by omega)]
    exact hread t ht
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.meets (d := d + 1) (μ := μ₁) (dst := dst + 4) S hw (by omega) hkey hj (by omega) hsep hspace hdecodeWord hread₁) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightOutputDecodeOriginal.meets (d := d + 1) (μ := μ₁) (dst := dst + 4) S hw (by omega) hkey hj (by omega) hsep hspace hdecodeWord hread₁) ?_ ?_ ?_ ?_
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
     on_goal -1 => (rintro bank ν ⟨hbank', rows, kept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst (s : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 1) (q : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hquot']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hquot'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hquot'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 2) (j : ℕ) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + 3) (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbank']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbank'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbank'] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hbank']
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hbank'] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hbank'] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine ⟨rfl,⟨?_,?_,?_,?_,?_⟩,?_⟩
  · simp [s]
  · simp [q]
  · simp
  · simp
  · constructor
    · intro t
      change Function.update (Function.update (Function.update (Function.update ν dst (s : ℤ))
        (dst+1) (q : ℤ)) (dst+2) (j : ℤ)) (dst+3)
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℤ)
        (dst+4+t.val)=_
      simp only [Function.update_of_ne (show dst+4+t.val ≠ dst+3 by omega),
        Function.update_of_ne (show dst+4+t.val ≠ dst+2 by omega),
        Function.update_of_ne (show dst+4+t.val ≠ dst+1 by omega),
        Function.update_of_ne (show dst+4+t.val ≠ dst by omega)]
      exact rows.occurrences t
    · intro t
      change Function.update (Function.update (Function.update (Function.update ν dst (s : ℤ))
        (dst+1) (q : ℤ)) (dst+2) (j : ℤ)) (dst+3)
        (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℤ)
        (dst+4+J+t.val)=_
      simp only [Function.update_of_ne (show dst+4+J+t.val ≠ dst+3 by omega),
        Function.update_of_ne (show dst+4+J+t.val ≠ dst+2 by omega),
        Function.update_of_ne (show dst+4+J+t.val ≠ dst+1 by omega),
        Function.update_of_ne (show dst+4+J+t.val ≠ dst by omega)]
      exact rows.masks t
  · intro a ha
    change Function.update (Function.update (Function.update (Function.update ν dst (s : ℤ))
      (dst+1) (q : ℤ)) (dst+2) (j : ℤ)) (dst+3)
      (_root_.ThreeSum.OutputDecodeOccurrenceCode.code (_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h) (_root_.ThreeSum1960614.Machine.ThreeSum.OutputDecodeRecords.layerCount h) J j : ℤ) a=μ a
    rw [Function.update_of_ne (show a ≠ dst+3 by omega),
      Function.update_of_ne (show a ≠ dst+2 by omega),
      Function.update_of_ne (show a ≠ dst+1 by omega),
      Function.update_of_ne (show a ≠ dst by omega),kept _ (by omega),hkeep₁ _ (by omega)]
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.meets__implementation_291166e7b2) := (@ThreeSum1960614.Machine.ThreeSum.LightWantedDecode.meets__implementation_291166e7b2)

#print axioms solution
