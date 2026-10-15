-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:39:38.250969+00:00
-- url     : https://prove2.me/submissions/4d9c229f-3b16-4ce0-9ec5-d930f86a948c

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle028
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_for
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightQueryEnumeration_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSubsetEnumerationSetup_meets
import Theorems.Thm_ThreeSum_MaskDifference_subsetMask_union_sdiff
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_leftAt_card
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_lefts_length
import Theorems.Thm_ThreeSum_ReportingHostPairEnumeration_rights_length

namespace Finset
end Finset
namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LayerCounts
end ThreeSum.LayerCounts
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LightPascal
end ThreeSum.LightPascal
namespace ThreeSum.LightReportingAffine
end ThreeSum.LightReportingAffine
namespace ThreeSum.LightReportingPairRows
end ThreeSum.LightReportingPairRows
namespace ThreeSum.LightSubsetAddress
end ThreeSum.LightSubsetAddress
namespace ThreeSum.LocalGraph
end ThreeSum.LocalGraph
namespace ThreeSum.MaskDifference
end ThreeSum.MaskDifference
namespace ThreeSum.ReportingHostPairEnumeration
end ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum.SubsetAddress
end ThreeSum.SubsetAddress
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LayerCounts
end ThreeSum1960614.Machine.ThreeSum.LayerCounts
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray
namespace ThreeSum1960614.Machine.ThreeSum.LightPascal
end ThreeSum1960614.Machine.ThreeSum.LightPascal
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingAffine
end ThreeSum1960614.Machine.ThreeSum.LightReportingAffine
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows
end ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows
namespace ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
end ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
namespace ThreeSum1960614.Machine.ThreeSum.LocalGraph
end ThreeSum1960614.Machine.ThreeSum.LocalGraph
namespace ThreeSum1960614.Machine.ThreeSum.MaskDifference
end ThreeSum1960614.Machine.ThreeSum.MaskDifference
namespace ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
end ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
namespace ThreeSum1960614.Machine.ThreeSum.SubsetAddress
end ThreeSum1960614.Machine.ThreeSum.SubsetAddress

namespace ThreeSum1960614.Machine

/-!
# Exact counts for the local subset graph

These are counts of the executable finite sets used by the graph, rather
than abstract numerical cardinality hypotheses.  An edge is an ordered
pair of disjoint `h`-subsets of `Fin L`.
-/

namespace ThreeSum.LayerCounts
open _root_.ThreeSum.LayerCounts


open _root_.Finset

















theorem vertex_degree_identity (L h : ℕ) :
    L.choose h * (L - h).choose h = L.choose (2 * h) * (2 * h).choose h := by
  simpa [show 2 * h - h = h by omega] using
    (Nat.choose_mul (n := L) (k := 2 * h) (s := h) (by omega)).symm



end ThreeSum.LayerCounts

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









theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ)-(_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) := by
  have h := _root_.ThreeSum.MaskDifference.subsetMask_union_sdiff Q U hU
  have hz : (_root_.ThreeSum.SubsetAddress.subsetMask U : ℤ)+(_root_.ThreeSum.SubsetAddress.subsetMask (Q \ U) : ℤ) = (_root_.ThreeSum.SubsetAddress.subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Proof rules for the light language

Ends lim P d s σ T Q says: the statement s, started in σ, ends within T steps in a state that
satisfies Q.  There is one rule for each construct; a rule turns a goal about a statement into goals
about its parts, so a proof follows the text of the program from top to bottom.  Recursion needs no
rule: a statement about a recursive procedure is proved by induction (in Lean) on a measure, and the
rule for calls unfolds the body.

There are three rules for loops: with an invariant indexed by the number of the round and a cost for
each round (Ends.while), the same with one cost for all rounds (Ends.whileConst), and, for a loop
whose number of rounds depends on the data, with a quantity that every round decreases
(Ends.whileVariant).

The file also has the basic facts about runs (a run stays a run when procedures are appended to the
program), notation for writing programs, the simplification set
`light_norm`, and the standing assumptions `Std` about the limits.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Runs -/









/-! ## The rules -/





























/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame





/-- The natural number behind an address that is a sum of two natural numbers. -/
@[simp] theorem toNat_natCast_add_natCast (a b : ℕ) : ((a : ℤ) + (b : ℤ)).toNat = a + b := by
  rw [← Nat.cast_add, Int.toNat_natCast]

/-! ## The limits -/









end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Regions of the memory, and the cells that a step leaves alone

A region is given by its first address `a` and its number `n` of cells.  `Inside a n b` says that
the cell `b` lies in it, `Outside a n b` that it does not, and `Apart a n a' n'` that two regions do
not meet.  `InOrder top [(a, n), (a', n'), …]` says that the listed regions lie one behind the other
and end at or below `top`.  All of these abbreviate linear inequalities.

`SameOn K μ μ'` says that the memory `μ'` agrees with `μ` on every cell that satisfies `K`.  It is
the one notion of "these cells are unchanged": a routine promises `SameOn K μ μ'` for the cells
`K` that it leaves alone.  (It is `Set.EqOn μ' μ {b | K b}`, stated with a predicate: the conditions
`K b` that occur are linear inequalities between addresses and are used as such.)  The usual choices
of `K` have names.

* `SameOutside μ μ' a n`: all cells outside one region; `SameOutside2` and `SameOutside3`: all cells
  outside two or three regions.
* `Kept μ μ' fr`: all cells below the free pointer `fr`.
* `KeptBut μ μ' fr out len`: all cells below `fr` outside the region of an output.

## How a fact is carried from one memory to a later one

A predicate `X` about a memory has one lemma of the name `X.keep` and of the form

  `theorem X.keep (h : X μ …) (hs : SameOn K μ μ' := by light_keep) : X μ' …`

where `K` describes the cells that `X` reads; `Seg.keep` is the model.  The argument `hs` has a
default proof.  So `h.keep`, with no argument, stands for "`h` still holds in the memory that is
asked for here".  The default proof `light_keep` uses every hypothesis of the form `SameOn _ ν ν'`
in the context, that is, the promises of the steps that were taken since `h` was obtained, and the
inequalities in the context that say where the regions lie.  In the proofs a promise is named when
the step is taken, as `same₂` in `rintro _ μ₂ ⟨sY, same₂⟩`.

`wrote μ dst f j` is the memory `μ` after a loop has written `f 0`, …, `f (j - 1)` to the cells from
`dst`.
-/

@[expose] public section

namespace Light
open _root_.Light


/-! ## Regions -/









/-! ## Memories that agree on some cells -/













variable {K K' K₁ K₂ : ℕ → Prop} {μ μ' μ'' : ℕ → ℤ} {b : ℕ}













/-! ## Writing a region cell by cell -/

variable {dst j : ℕ} {f : ℕ → ℤ}





/-- A cell that has been written. -/
theorem wrote_done {i : ℕ} (h : i < j) : _root_.Light.wrote μ dst f j (dst + i) = f i := by
  unfold _root_.Light.wrote
  rw [if_pos (by omega), Nat.add_sub_cancel_left]

/-- A cell that has not been written (yet). -/
theorem wrote_rest {a : ℕ} (h : _root_.Light.Outside dst j a) : _root_.Light.wrote μ dst f j a = μ a := by
  unfold _root_.Light.wrote
  rw [if_neg (by omega)]







/-! ## The tactics -/











end Light

end

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
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray
open _root_.ThreeSum.LightArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



theorem source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : _root_.ThreeSum.LightArray.SourceSafe src dst n) (hj : j < n) :
    _root_.Light.wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)
  · exact _root_.ThreeSum1960614.Machine.Light.wrote_rest (by omega)











end ThreeSum.LightArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # Costed affine scans used to form reporting child-prefix masks -/

namespace ThreeSum.LightReportingAffine
open _root_.ThreeSum.LightReportingAffine


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightArray

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem meets {p src dst n : ℕ} {b c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : _root_.ThreeSum.LightArray.SourceSafe src dst n)
    (hmul : ∀ i < n, |c*μ (src+i)| ≤ lim.word)
    (hsum : ∀ i < n, |b+c*μ (src+i)| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [src,dst,n,b,c] μ (_root_.ThreeSum.LightReportingAffine.time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = b+c*μ (src+i)) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n) := by
  refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun i => b+c*μ (src+i))
    (fun i hi => ?_) ⟨fun i hi => _root_.ThreeSum1960614.Machine.Light.wrote_done (f := fun i => b+c*μ (src+i)) hi,
      by (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
            intro p2m_macro_12545772195636606797 p2m_macro_4265689903731703288
            first
            | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_4322064052873904471); (try have := p2m_macro_4322064052873904471 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_4322064052873904471)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            |
              (simp [] at p2m_macro_4265689903731703288;
                ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_11945687192546809425); (try have := p2m_macro_11945687192546809425 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_11945687192546809425)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
            | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_17476295892461720639); (try have := p2m_macro_17476295892461720639 p2m_macro_12545772195636606797 (by omega)); revert p2m_macro_17476295892461720639)
                  intros
                  try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                            SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                            its condition K x does not follow from the hypotheses.")))⟩ hw hdst rfl rfl (hT := by (first
                                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingAffine.time]
                                                    first
                                                    | omega
                                                    | (ring_nf; omega))
                                                | omega
                                                |
                                                  (simp [_root_.ThreeSum.LightReportingAffine.time] <;>
                                                      first
                                                      | omega
                                                      | (ring_nf; omega)))))
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.source_read (μ := μ) (f := fun i => b+c*μ (src+i)) hsep hi
  have hm := abs_le.mp (hmul i hi)
  have hs := abs_le.mp (hsum i hi)
  (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr] <;> omega))





end ThreeSum.LightReportingAffine

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A direct ordered enumeration of every local balanced row pair

First enumerate the h-subsets, then enumerate h-subsets of each complement.
The list contains every edge exactly once and has the exact local catalog
size, without scanning the ambient Boolean cube or all pairs of vertices.
-/

namespace ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum.ReportingHostPairEnumeration


open _root_.Finset
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LayerCounts
open _root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts
open _root_.ThreeSum.LocalGraph
open _root_.ThreeSum1960614.Machine.ThreeSum.LocalGraph

set_option linter.unusedSimpArgs false













theorem lefts_masks (L h : ℕ) : (_root_.ThreeSum.ReportingHostPairEnumeration.lefts L h).map _root_.ThreeSum.SubsetAddress.subsetMask = _root_.ThreeSum.SubsetAddress.enumerateLayer L h := by
  apply List.ext_getElem
  · simp [_root_.ThreeSum.ReportingHostPairEnumeration.lefts]
  · intro i hi hi'
    simp only [List.getElem_map,_root_.ThreeSum.ReportingHostPairEnumeration.lefts,List.getElem_map]
    exact _root_.ThreeSum.MaskDecode.subsetMask_decode ((_root_.ThreeSum.SubsetAddress.mem_enumerateLayer L h _).mp (List.getElem_mem hi')).1

















theorem leftAt_eq_get {L h i : ℕ} (hi : i < L.choose h) :
    _root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i = (_root_.ThreeSum.ReportingHostPairEnumeration.lefts L h)[i]'(by simpa using hi) := by
  simp [_root_.ThreeSum.ReportingHostPairEnumeration.leftAt,List.getElem?_eq_getElem,hi]



theorem rightAt_eq_get {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    _root_.ThreeSum.ReportingHostPairEnumeration.rightAt L h i j = (_root_.ThreeSum.ReportingHostPairEnumeration.rights (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) h)[j]'(by rw [_root_.ThreeSum.ReportingHostPairEnumeration.rights_length _ (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt_card hi)]; exact hj) := by
  have hlen : j < (_root_.ThreeSum.ReportingHostPairEnumeration.rights (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) h).length := by rw [_root_.ThreeSum.ReportingHostPairEnumeration.rights_length _ (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt_card hi)]; exact hj
  simp [_root_.ThreeSum.ReportingHostPairEnumeration.rightAt,List.getElem?_eq_getElem hlen]



theorem subsetMask_univ_succ (L : ℕ) : _root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L))+1 = 2^L := by
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sum,Fin.sum_univ_eq_sum_range]
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ,Nat.pow_succ]
      omega

theorem leftAt_mask {L h i : ℕ} (hi : i < L.choose h) :
    _root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) = (_root_.ThreeSum.SubsetAddress.enumerateLayer L h)[i]'(by rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]; exact hi) := by
  have hiL : i < (_root_.ThreeSum.ReportingHostPairEnumeration.lefts L h).length := by rw [_root_.ThreeSum.ReportingHostPairEnumeration.lefts_length]; exact hi
  have hiE : i < (_root_.ThreeSum.SubsetAddress.enumerateLayer L h).length := by rw [_root_.ThreeSum.SubsetAddress.enumerateLayer_length]; exact hi
  have he := congrArg (fun xs : List ℕ => xs[i]?.getD 0) (_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.lefts_masks L h)
  rw [_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.leftAt_eq_get hi]
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hiL,
    List.getElem?_eq_getElem hiE,Option.map_some,Option.getD_some] using he

end ThreeSum.ReportingHostPairEnumeration

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightReportingPairRows
open _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.SubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.SubsetAddress
open _root_.ThreeSum.LightPascal
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPascal
open _root_.ThreeSum.LightSubsetAddress
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetAddress
open _root_.ThreeSum.ReportingHostPairEnumeration
open _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration
set_option maxHeartbeats 1800000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program_meets__implementation_b8c6806ba4 {μ : ℕ → ℤ} {L h srcS dstL dstR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ dstL)
    (hL : dstL+L.choose h*(L-h).choose h ≤ dstR)
    (hR : dstR+L.choose h*(L-h).choose h ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+3 ≤ lim.depth) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program 7 d [L,h,srcS,dstL,dstR,work] μ (_root_.ThreeSum.LightReportingPairRows.time L h)
      (fun r μ' => r = (L.choose (2*h)*(2*h).choose h : ℤ) ∧
        _root_.ThreeSum1960614.Machine.Light.SegN μ' srcS (_root_.ThreeSum.SubsetAddress.enumerateLayer L h) ∧
        (∀ i < L.choose h, ∀ j < (L-h).choose h,
          μ' (dstL+i*(L-h).choose h+j) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h i) : ℤ) ∧
          μ' (dstR+i*(L-h).choose h+j) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.rightAt L h i j) : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ μ' srcS) := by
  have hdeg : 0 < (L-h).choose h := Nat.choose_pos (by omega)
  have hverts : 0 < L.choose h := Nat.choose_pos (by omega)
  have hmask (S : Finset (Fin L)) : (_root_.ThreeSum.SubsetAddress.subsetMask S : ℤ) ≤ lim.word := by
    have hb : _root_.ThreeSum.SubsetAddress.subsetMask S ≤ 2^(L+1) := (Nat.le_of_lt (_root_.ThreeSum.SubsetAddress.subsetMask_isMask S).1).trans
      (Nat.pow_le_pow_right (by decide) (by omega))
    exact (Int.ofNat_le.mpr hb).trans hword
  have hfullWord := hmask (Finset.univ : Finset (Fin L))
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body (p := 7) (by rfl : program[7]? = some (body 5 0 6))
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.body _root_.ThreeSum.LightReportingPairRows.time
  have hs := _root_.ThreeSum1960614.Machine.ThreeSum.LightSubsetEnumerationSetup.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program) (pMain := 5) (pPowers := 2)
    (pEnum := 4) (d := d+1) (μ := μ) (L := L) (k := h) (dst := srcS) (work := work)
    rfl rfl rfl hw (by omega) hword (by omega) (by omega) (by omega)
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
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
     on_goal -1 => (rintro len μ₁ ⟨hlen, hlefts, hpowers, hkeepLayer⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  subst len
  have hpow := hpowers L le_rfl
  have hpowNat : μ₁ (work+L) = ((2^L : ℕ) : ℤ) := by simpa using hpow
  have hfull : ((2^L : ℕ) : ℤ)-1 = (_root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L)) : ℤ) := by
    have he : (_root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L)) : ℤ)+1 = ((2^L : ℕ) : ℤ) := by
      exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.subsetMask_univ_succ L
    omega
  have hfullInt : (2 : ℤ)^L-1 = (_root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L)) : ℤ) := by simpa using hfull
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L)) : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpow, hpowNat, hfull, hfullInt, _root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [hpow, hpowNat, hfull, hfullInt, _root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpow, hpowNat, hfull, hfullInt, _root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (0 : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSubsetEnumerationSetup.time, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen (_root_.ThreeSum1960614.Machine.Light.Ends.for (lim := lim) (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program) (d := d) (i := 9) (hi := _root_.ThreeSum1960614.Machine.Light.v 6)
    (body := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.roundBody 0 6) (T := L.choose h*(_root_.ThreeSum.LightReportingPairRows.roundTime L h+20)+70)
    (Q := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.Inv μ L h srcS dstL dstR work (L.choose h))
    (_root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.Inv μ L h srcS dstL dstR work) (L.choose h) (_root_.ThreeSum.LightReportingPairRows.roundTime L h)
    ?start ?round ?done ?bound (hT := by (first
                                          | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPairRows.roundTime]
                                              first
                                              | omega
                                              | (ring_nf; omega))
                                          | omega
                                          |
                                            (simp [_root_.ThreeSum.LightReportingPairRows.roundTime] <;>
                                                first
                                                | omega
                                                | (ring_nf; omega))))) ?after
  case start =>
    refine ⟨0,0,0,0,μ₁,?_,hlefts,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      change _root_.Light.frame [(L : ℤ),h,srcS,dstL,dstR,work,L.choose h,
        _root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L)),0,0] =
        _root_.Light.frame ([(L : ℤ),h,srcS,dstL,dstR,work,L.choose h,
          _root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ : Finset (Fin L)),0,0] ++ [0,0,0,0])
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 4).symm
    · intro i hi; omega
    · intro i hi
      exact hkeepLayer i ⟨by omega,Or.inl hi⟩
  case round =>
    rintro j _ hj _ ⟨a,b,nr,r,μ',rfl,hlefts,hout,hkeep⟩
    have hjD : j*(L-h).choose h+(L-h).choose h ≤ L.choose h*(L-h).choose h := by
      have hm := Nat.mul_le_mul_right ((L-h).choose h) (show j+1 ≤ L.choose h by omega)
      nlinarith
    have hleftCard := _root_.ThreeSum.ReportingHostPairEnumeration.leftAt_card hj
    have hcomp : (Finset.univ \ _root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j).card = L-h := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),Finset.card_univ,Fintype.card_fin,hleftCard]
    have hread : μ' (srcS+j) = (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) : ℤ) := by
      have hget := hlefts j (by simpa only [List.length_map,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] using hj)
      simpa only [List.getElem_map,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.leftAt_mask hj] using hget
    have hlword := hmask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j)
    have hcword := hmask (Finset.univ \ _root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j)
    have hdiff := _root_.ThreeSum1960614.Machine.ThreeSum.MaskDifference.subsetMask_sdiff_int Finset.univ (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) (Finset.subset_univ _)
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.roundBody
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hread, _root_.ThreeSum.LightReportingPairRows.roundTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hread, _root_.ThreeSum.LightReportingPairRows.roundTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hread, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ \ _root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hdiff, _root_.ThreeSum.LightReportingPairRows.roundTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hdiff, _root_.ThreeSum.LightReportingPairRows.roundTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hdiff, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hq := _root_.ThreeSum1960614.Machine.ThreeSum.LightQueryEnumeration.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program) (pMain := 0) (pWeights := 1)
      (pPowers := 2) (pErase := 3) (pEnum := 4) (d := d+1) (μ := μ')
      (dst := dstR+j*(L-h).choose h) (work := work) (t := h)
      rfl rfl rfl rfl rfl (Finset.univ \ _root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) hw (by omega) hword
      (by rw [hcomp]; omega) (by rw [hcomp]; omega) (by omega)
    rw [hcomp] at hq
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hq _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hq ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPairRows.roundTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightReportingPairRows.roundTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
       on_goal -1 => (rintro count ν ⟨hcount, hnewR, hweights, hkeepQuery⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have ha := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.meets (P := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program) (p := 6) (d := d+1)
      (μ := ν) (src := dstR+j*(L-h).choose h) (dst := dstL+j*(L-h).choose h)
      (n := (L-h).choose h) (b := (_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) : ℤ)) (c := 0)
      rfl hw (by omega) (by omega) (Or.inr (by omega))
      (by intro i hi; simp only [zero_mul,abs_zero]; omega)
      (by intro i hi; simpa only [zero_mul,add_zero,Int.abs_natCast] using hlword)
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (ha _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ha ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, _root_.ThreeSum.LightReportingPairRows.roundTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcount, _root_.ThreeSum.LightReportingPairRows.roundTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
       on_goal -1 => (rintro affineRet ξ ⟨hnewL, hkeepAffine⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen ((j + 1) * (L - h).choose h : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, Nat.add_mul, _root_.ThreeSum.LightReportingPairRows.roundTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hcount, Nat.add_mul, _root_.ThreeSum.LightReportingPairRows.roundTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, Nat.add_mul, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,(_root_.ThreeSum.SubsetAddress.subsetMask (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) : ℤ),
      (_root_.ThreeSum.SubsetAddress.subsetMask (Finset.univ \ _root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) : ℤ),count,affineRet,ξ,?_,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · intro i hi
      rw [hkeepAffine (srcS+i) (Or.inl (by simp only [List.length_map,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] at hi; omega)),
        hkeepQuery (srcS+i) ⟨by simp only [List.length_map,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] at hi; omega,
          Or.inl (by simp only [List.length_map,_root_.ThreeSum.SubsetAddress.enumerateLayer_length] at hi; omega)⟩]
      exact hlefts i hi
    · intro i hi l hl
      by_cases he : i = j
      · subst i
        constructor
        · simpa only [zero_mul,add_zero,Nat.add_assoc] using hnewL l hl
        · rw [hkeepAffine _ (Or.inr (by omega))]
          have hlen : l < (_root_.ThreeSum.ReportingHostPairEnumeration.rights (_root_.ThreeSum.ReportingHostPairEnumeration.leftAt L h j) h).length := by rw [_root_.ThreeSum.ReportingHostPairEnumeration.rights_length _ hleftCard]; exact hl
          have hr := hnewR l (by simpa only [List.length_map,_root_.ThreeSum.ReportingHostPairEnumeration.rights] using hlen)
          simpa only [List.getElem_map,Nat.add_assoc,_root_.ThreeSum.ReportingHostPairEnumeration.rights,_root_.ThreeSum1960614.Machine.ThreeSum.ReportingHostPairEnumeration.rightAt_eq_get hj hl] using hr
      · have hij : i < j := by omega
        have hm := Nat.mul_le_mul_right ((L-h).choose h) (show i+1 ≤ j by omega)
        obtain ⟨hprevL,hprevR⟩ := hout i hij l hl
        constructor
        · rw [hkeepAffine _ (Or.inl (by nlinarith)),hkeepQuery _ ⟨by nlinarith,Or.inl (by nlinarith)⟩]
          exact hprevL
        · rw [hkeepAffine _ (Or.inr (by omega)),hkeepQuery _ ⟨by nlinarith,Or.inl (by nlinarith)⟩]
          exact hprevR
    · intro i hi
      exact (hkeepAffine i (Or.inl (by omega))).trans
        ((hkeepQuery i ⟨by omega,Or.inl (by omega)⟩).trans (hkeep i hi))
  case done =>
    intro σ _ hσ
    exact hσ
  case bound =>
    rintro j _ hj _ ⟨a,b,nr,r,μ',rfl,_,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
  case after =>
    rintro _ ⟨a,b,nr,r,μ',rfl,hlefts,hout,hkeep⟩
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (L.choose h * (L - h).choose h : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightReportingPairRows.roundTime]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightReportingPairRows.roundTime] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightReportingPairRows.roundTime] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨?_,hlefts,hout,hkeep⟩
    simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LayerCounts.vertex_degree_identity]
    rfl
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program_meets__implementation_b8c6806ba4) := (@ThreeSum1960614.Machine.ThreeSum.LightReportingPairRows.program_meets__implementation_b8c6806ba4)

#print axioms solution
