-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:36:13.86423+00:00
-- url     : https://prove2.me/submissions/cab4a33a-9fe2-4d94-a1dc-900d9d61d4e9

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
import Definitions.Def_ThreeSum1962Source_Bundle13
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
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Base
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
import Mathlib.Data.List.Sublists
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
import Mathlib.Tactic.LinearCombination
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_BlockSourceCoverInput_Input_of_kept
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBlockSourceBatchStep_Procs_meets
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
namespace ThreeSum.BlockSourceEncoding
end ThreeSum.BlockSourceEncoding
namespace ThreeSum.LightBlockSourceBatch
end ThreeSum.LightBlockSourceBatch
namespace ThreeSum.LightBlockSourceBatchLayout
end ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum.LightSourceResidues
end ThreeSum.LightSourceResidues
namespace ThreeSum.LightZetaStages
end ThreeSum.LightZetaStages
namespace ThreeSum.LocalCoverBounds
end ThreeSum.LocalCoverBounds
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
namespace ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
end ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
namespace ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
end ThreeSum1960614.Machine.ThreeSum.GlobalEncoding
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
end ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
namespace ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
end ThreeSum1960614.Machine.ThreeSum.LightSourceResidues
namespace ThreeSum1960614.Machine.ThreeSum.LightZetaStages
end ThreeSum1960614.Machine.ThreeSum.LightZetaStages
namespace ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
end ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
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
# Local variables as a list

In the proof of a procedure body the state is written out as ⟨frame [a, b, …], μ⟩: the list
holds the local variables 0, 1, …, and all further ones are 0.  An assignment to local x replaces
entry x of the list (setLocal).  The rules of this file treat one statement each.  They are told the
value that is assigned or stored, and they ask for one fact about each expression: that its
evaluation stays within the limits and gives this value (Expr.Gives).  This fact and the comparison
of the costs are proved by default from the hypotheses in the context.  Ends.forFrame and
Ends.forShape are the rules for counting loops in this form.  In the names of the rules, To says
that the state is ⟨frame l, μ⟩.

Locals by name, and locals whose values do not matter:

* `setLocals l [(x, a), (y, b), …]` is the list `l` after the assignments `x := a`, `y := b`, ….
  With the names of the locals for `x`, `y`, … it describes the locals of a procedure by name:
  `setLocals [] [(Size, n), (Bound, U), …]`.
* `updateLocals loc [(x, a), (y, b), …]` is the same for locals that are not given as a list.  A
  lemma about a piece of text that several procedures share is stated for arbitrary locals `loc`.
* `refreshLocals l loc xs` is the list `l` with the entries `xs` read from `loc`.
* `LocalsBut xs l loc` says that `loc` agrees with `frame l` except perhaps at the locals `xs`.  In
  an invariant, `xs` are the scratch variables.  `Ends.asFrame` goes from such locals to a list, and
  `LocalsBut.of_eq` comes back.
* `Ends.pieceTo` and `Ends.pieceToThen` use a lemma about a piece of text that assigns only the
  locals `xs`: afterwards the locals are `refreshLocals l loc' xs`, where `loc'` are the locals of
  which the lemma speaks.  The lemma need not mention the locals that the piece does not assign.
* `Ends.forScratch` is the rule for a counting loop whose body may change the scratch variables
  `xs`: the round says nothing about the locals.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## The list of the locals -/







/-- Zeros at the end of the list do not matter. -/
theorem frame_append_zeros (l : List ℤ) (n : ℕ) : _root_.Light.frame (l ++ List.replicate n 0) = _root_.Light.frame l := by
  funext y
  simp only [_root_.Light.frame, List.getD_eq_getElem?_getD, List.getElem?_append, List.getElem?_replicate]
  split_ifs with h1 h2
  · rfl
  · rw [List.getElem?_eq_none (by omega)]
    rfl
  · rw [List.getElem?_eq_none (by omega)]

/-! ## The value of an expression -/



/-! ## One statement -/

section rules

variable {l : List ℤ} {μ : ℕ → ℤ} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}

















end rules

/-! ## Locals by name, and locals whose values do not matter -/























section
variable {xs : List ℕ} {l l' : List ℤ} {loc μ : ℕ → ℤ}







/-! ## A piece of program text with a lemma of its own -/

variable {T T₁ : ℕ} {s s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q R : _root_.ThreeSum1960614.Machine.Light.State → Prop}







/-! ## Counting loops with scratch variables -/



end

end Light

end

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

/-!
# Packed retained source banks indexed by occurrence vectors

Each bank retains its compact masks, coefficients, endpoints, flags, and
both complete source-stage families. Shared temporary transform workspace
follows all banks. Two header cells per occurrence contain the stage bases.
This layout lets the next actual source call preserve every earlier bank.
-/

namespace ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum.LightBlockSourceBatchLayout


open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightZetaStages
open _root_.ThreeSum1960614.Machine.ThreeSum.LightZetaStages

















theorem banks_le_slot (base count W cut i : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i :=
  Nat.le_add_right _ _

theorem slot_mono (base count W cut : ℕ) : Monotone (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem left_ge_slot (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0
  omega

theorem right_ge_left (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i := Nat.le_add_right _ _

theorem right_end (base count W cut i : ℕ) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut = _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase _root_.ThreeSum.LightBlockSourceBatchLayout.flags _root_.ThreeSum.LightBlockSourceBatchLayout.rawRight _root_.ThreeSum.LightBlockSourceBatchLayout.rawLeft _root_.ThreeSum.LightBlockSourceBatchLayout.coeff1 _root_.ThreeSum.LightBlockSourceBatchLayout.coeff0 _root_.ThreeSum.LightBlockSourceBatchLayout.slot _root_.ThreeSum.LightBlockSourceBatchLayout.stride
  ring





theorem banks_le_work (base count W cut : ℕ) : _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.work base count W cut := by
  have hm := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut count
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.work _root_.ThreeSum.LightBlockSourceBatchLayout.rowOut _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase _root_.ThreeSum.LightBlockSourceBatchLayout.maskBase
  omega



theorem header_end_le_slot {base count W cut i : ℕ} (hi : i < count) :
    base+2*i+2 ≤ _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut i := by
  have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut i
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
  omega





theorem stage_cell_lt_end {W cut base j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase base (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S < base+_root_.ThreeSum.LightBlockSourceBatchLayout.family W cut := by
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress.subsetRank_lt hS
  have hm := Nat.mul_le_mul_right (_root_.ThreeSum.SubsetAddress.downsetCap W cut) (Nat.succ_le_succ hj)
  calc
    _ < base+j*_root_.ThreeSum.SubsetAddress.downsetCap W cut+_root_.ThreeSum.SubsetAddress.downsetCap W cut := Nat.add_lt_add_left hr _
    _ = base+(j+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut := by ring
    _ ≤ base+(W+1)*_root_.ThreeSum.SubsetAddress.downsetCap W cut := Nat.add_le_add_left hm _
    _ = _ := rfl

theorem left_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S <
      _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.stage_cell_lt_end (base := _root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i) hj hS
  have he := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end base count W cut i
  unfold _root_.ThreeSum.LightBlockSourceBatchLayout.rightBase at he
  omega

theorem right_cell_lt_next {base count W cut i j : ℕ} {S : Finset (Fin W)}
    (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S <
      _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut (i+1) := by
  rw [← _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_end]
  exact _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.stage_cell_lt_end hj hS

theorem left_cell_lt_later {base count W cut i k j : ℕ} {S : Finset (Fin W)}
    (hik : i < k) (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S <
      _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut k :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.left_cell_lt_next hj hS).trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.slot_mono base count W cut (by omega))

theorem right_cell_lt_later {base count W cut i k j : ℕ} {S : Finset (Fin W)}
    (hik : i < k) (hj : j ≤ W) (hS : S.card ≤ cut) :
    _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S <
      _root_.ThreeSum.LightBlockSourceBatchLayout.slot base count W cut k :=
  (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_cell_lt_next hj hS).trans_le (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.slot_mono base count W cut (by omega))

theorem banks_le_left_cell (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.leftBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S := by
  have hs := (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut i).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.left_ge_slot base count W cut i)
  unfold _root_.ThreeSum.LightZetaStages.stageBase
  omega

theorem banks_le_right_cell (base count W cut i j : ℕ) (S : Finset (Fin W)) :
    _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count ≤ _root_.ThreeSum.LightZetaStages.stageBase (_root_.ThreeSum.LightBlockSourceBatchLayout.rightBase base count W cut i) (_root_.ThreeSum.SubsetAddress.downsetCap W cut) j+_root_.ThreeSum.SubsetAddress.subsetRank S := by
  have hs := ((_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count W cut i).trans
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.left_ge_slot base count W cut i)).trans (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_ge_left base count W cut i)
  unfold _root_.ThreeSum.LightZetaStages.stageBase
  omega

end ThreeSum.LightBlockSourceBatchLayout

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Actual shared source-stage catalog over occurrence vectors

One loop iteration constructs one retained bank and its two header pointers.
The original-band histograms and local-cover data are read throughout and
preserved. The semantic occurrence-row contract labels an ordinary physical
array; it does not assume any source-stage computation or output-subset loop.
-/

namespace ThreeSum.LightBlockSourceBatch
open _root_.ThreeSum.LightBlockSourceBatch


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
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000



theorem BankAt.of_later {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i k : ℕ} {μ ν : ℕ → ℤ} {P shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J}
    (H : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt μ base count cut i P shift B b A a q)
    (K : _root_.ThreeSum1960614.Machine.Light.KeptBut μ ν (_root_.ThreeSum.LightBlockSourceBatchLayout.slot base count (J*(464*h)) cut k) (base+2*k) 2)
    (hik : i < k) (hk : k < count) : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt ν base count cut i P shift B b A a q := by
  have hhead := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.header_end_le_slot (base := base) (W := J*(464*h)) (cut := cut) hk
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj S hS
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_left_cell base count (J*(464*h)) cut i j S
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
    exact (K _ ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.left_cell_lt_later hik hj hS,Or.inr (by omega)⟩).trans (H.left j hj S hS)
  · intro j hj S hS
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_right_cell base count (J*(464*h)) cut i j S
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
    exact (K _ ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.right_cell_lt_later hik hj hS,Or.inr (by omega)⟩).trans (H.right j hj S hS)
  · exact (K _ ⟨by omega,Or.inl (by omega)⟩).trans H.headerLeft
  · exact (K _ ⟨by omega,Or.inl (by omega)⟩).trans H.headerRight











variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



end ThreeSum.LightBlockSourceBatch

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch

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
open _root_.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds
open _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding
open _root_.ThreeSum.LightBlockSourceBatchLayout
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout
set_option maxHeartbeats 3500000
set_option maxRecDepth 16000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section


theorem ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs.meets__implementation_30950d07de {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {pMain : ℕ} (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs P pMain)
    {μ : ℕ → ℤ} {h J cut p NL NR occ maps candidates histL histR sourceHistL sourceHistR
      base count : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (A : Finset γ) (a : γ → ℤ)
    (q : ℕ → _root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.GlobalOutput h J) (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ A)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(464*h)+11 ≤ lim.depth)
    (hcut : cut ≤ J*(464*h))
    (hocc : occ+count*J ≤ base) (hmaps : maps+2*(464*h)*_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hcandidates : candidates+_root_.ThreeSum1960614.Machine.ThreeSum.GlobalEncoding.scheduleSize h ≤ base)
    (hleft : histL+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hright : histR+_root_.ThreeSum1960614.Machine.ThreeSum.LightLocalCoverSchedule.rows h*_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h ≤ base)
    (hsourceHistL : sourceHistL+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hsourceHistR : sourceHistR+_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J ≤ base)
    (hspace : _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.space (_root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut) h J ≤ lim.space)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceRetainedHost.word NL NR h J : ℤ) ≤ lim.word)
    (hinputL : ∀ j : Fin NL, vL j.val = b (eL j))
    (hinputR : ∀ j : Fin NR, vR j.val = a (eR j))
    (hhistReadL : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistL+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 vL NL r : ℤ))
    (hhistReadR : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
      μ (sourceHistR+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift vR NR r : ℤ))
    (hoccRead : ∀ i < count, ∀ j < J,
      μ (occ+i*J+j) = (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences (q i)) j : ℤ))
    (hcover : _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d
      [J,464*h,h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localPrime h,_root_.ThreeSum1960614.Machine.ThreeSum.LocalCoverBounds.localBucketCap h,cut,_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,occ,maps,candidates,
        histL,histR,sourceHistL,sourceHistR,base,_root_.ThreeSum.SubsetAddress.downsetCap (J*(464*h)) cut,count,
        _root_.ThreeSum.LightBlockSourceBatchLayout.banks base count,_root_.ThreeSum.LightBlockSourceBatchLayout.stride (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.maskBase base count (J*(464*h)) cut,
        _root_.ThreeSum.LightBlockSourceBatchLayout.bitBase base count (J*(464*h)) cut,_root_.ThreeSum.LightBlockSourceBatchLayout.rowOut base count (J*(464*h)) cut,
        _root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut]
      μ (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.time count h J cut) (fun _ ν =>
        (∀ i < count, _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.BankAt ν base count cut i (p : ℤ) shift B b A a (q i)) ∧ _root_.ThreeSum1960614.Machine.Light.Kept μ ν base) := by
  have hs : _root_.ThreeSum.LightBlockSourceBatchLayout.work base count (J*(464*h)) cut+(J*(464*h)+1) ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hbase : base ≤ lim.space := by
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_work base count (J*(464*h)) cut
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
    omega
  have hcount : count ≤ lim.space := by
    have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_work base count (J*(464*h)) cut
    unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
    omega
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.main
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.body _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.time
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Inv μ h J cut occ maps candidates histL histR sourceHistL sourceHistR base count
    (p : ℤ) shift B b A a q) count (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchStep.time h J cut+192)
    ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : _root_.ThreeSum1960614.Machine.Light.State))
        ((_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal _ _ _).trans (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hrow : occ+i*J+J ≤ base := by
      have hm := Nat.mul_le_mul_right J (show i+1 ≤ count by omega)
      nlinarith
    have hprodNat : i*J ≤ lim.space := by omega
    have hprod : (i : ℤ)*(J : ℤ) ≤ lim.word :=
      (by exact_mod_cast hprodNat : (i : ℤ)*(J : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : (0 : ℤ) ≤ (i : ℤ)*(J : ℤ) := by positivity
    have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
    have hhistL' : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
        ν (sourceHistL+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) 0 vL NL r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hhistReadL r hr)
    have hhistR' : ∀ r < _root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J,
        ν (sourceHistR+r) = (_root_.ThreeSum.LightBlockSourceRetainedStages.histogram p (_root_.ThreeSum1960614.Machine.ThreeSum.BlockSourceEncoding.modulus h J) shift vR NR r : ℤ) := by
      intro r hr
      exact (kept _ (by omega)).trans (hhistReadR r hr)
    have hocc' : ∀ j < J, ν (occ+i*J+j) =
        (_root_.ThreeSum1960614.Machine.ThreeSum.BlockCoefficientRows.occurrenceIndices (_root_.ThreeSum1960614.Machine.ThreeSum.BlockEncoding.outputOccurrences (q i)) j : ℤ) := by
      intro j hj
      exact (kept _ (by omega)).trans (hoccRead i hi j hj)
    have hrun := C.step.meets (d := d+1) (μ := ν) (cut := cut) (p := p) (shift := shift)
      (occ := occ+i*J) (maps := maps) (candidates := candidates) (histL := histL) (histR := histR)
      (sourceHistL := sourceHistL) (sourceHistR := sourceHistR) (base := base) (count := count) (i := i)
      B b A a (q i) vL vR eL eR hw (by omega) hcut hi hrow hmaps hcandidates hleft hright
      hsourceHistL hsourceHistR hspace hword hinputL hinputR hhistL' hhistR' hocc' hcover'
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hrun _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hrun ?_ ?_ ?_ ?_
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
       on_goal -1 => (rintro s ν' ⟨storedL, storedR, headL, headR, kept'⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,s,ν',by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (written j hj).of_later kept' hj hi
      · exact ⟨storedL,storedR,headL,headR⟩
    · intro a ha
      have hb := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatchLayout.banks_le_slot base count (J*(464*h)) cut i
      unfold _root_.ThreeSum.LightBlockSourceBatchLayout.banks at hb
      exact (kept' a ⟨by omega,Or.inl (by omega)⟩).trans (kept a ha)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    simp
end

end

theorem solution.{u_implementation_0,u_implementation_1} : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs.meets__implementation_30950d07de.{u_implementation_0,u_implementation_1}) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockSourceBatch.Procs.meets__implementation_30950d07de.{u_implementation_0,u_implementation_1})

#print axioms solution
