-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:26:12.447992+00:00
-- url     : https://prove2.me/submissions/b761cef9-0420-4a95-97bd-ab5c10705bd7

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle08
import Definitions.Def_ThreeSum1962Source_Bundle10
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
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_powTable_ends

namespace Light
end Light
namespace Light.PowTable
end Light.PowTable
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LightBlockCoefficients
end ThreeSum.LightBlockCoefficients
namespace ThreeSum.LightScaleArray
end ThreeSum.LightScaleArray
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.PowTable
end ThreeSum1960614.Machine.Light.PowTable
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray
namespace ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
end ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients
namespace ThreeSum1960614.Machine.ThreeSum.LightScaleArray
end ThreeSum1960614.Machine.ThreeSum.LightScaleArray

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

/-!
# Tables of powers

powTable(dst, L, b) writes 1, b, b², …, b^(L-1) into the L cells from dst and changes nothing else,
within `powTableTime L` steps (`powTable_meets`).  The list of these powers is `powList b L`.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



@[simp] theorem length_powList (b L : ℕ) : (_root_.Light.powList b L).length = L := by simp [_root_.Light.powList]

@[simp] theorem getElem_powList {b L j : ℕ} (h : j < (_root_.Light.powList b L).length) :
    (_root_.Light.powList b L)[j] = ((b ^ j : ℕ) : ℤ) := by
  simp [_root_.Light.powList]

namespace PowTable
open _root_.Light.PowTable








end PowTable

open _root_.Light.PowTable
open _root_.ThreeSum1960614.Machine.Light.PowTable











/-- **powTable(dst, L, b)** writes the powers 1, b, …, b^(L-1) into the L cells from dst and changes
nothing else. -/
theorem powTable_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody) {μ : ℕ → ℤ} {dst L b : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + L ≤ lim.space)
    (hpow : ∀ j ≤ L, ((b ^ j : ℕ) : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), L, b] μ (_root_.Light.powTableTime L) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (_root_.Light.powList b L) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L :=
  -- the local variables that are no arguments hold 0
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros [(dst : ℤ), L, b] 2 ▸ _root_.ThreeSum1960614.Machine.Light.powTable_ends 0 0 [] hw hdst hpow)

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-! # A costed array scaling pass -/

namespace ThreeSum.LightScaleArray
open _root_.ThreeSum.LightScaleArray


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.LightArray
open _root_.ThreeSum1960614.Machine.ThreeSum.LightArray

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





theorem meets {p src dst n : ℕ} {c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightScaleArray.body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : _root_.ThreeSum.LightArray.SourceSafe src dst n)
    (hword : ∀ i < n, |c*μ (src+i)| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [src,dst,n,c] μ (_root_.ThreeSum.LightScaleArray.time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = c*μ (src+i)) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n) := by
  refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun i => c*μ (src+i))
    (fun i hi => ?_) ⟨fun i hi => _root_.ThreeSum1960614.Machine.Light.wrote_done (f := fun i => c*μ (src+i)) hi,
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
                                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightScaleArray.time]
                                                    first
                                                    | omega
                                                    | (ring_nf; omega))
                                                | omega
                                                |
                                                  (simp [_root_.ThreeSum.LightScaleArray.time] <;>
                                                      first
                                                      | omega
                                                      | (ring_nf; omega)))))
  have hr := _root_.ThreeSum1960614.Machine.ThreeSum.LightArray.source_read (μ := μ) (f := fun i => c*μ (src+i)) hsep hi
  have hv := abs_le.mp (hword i hi)
  (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
     (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
     simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hr] <;> omega))





end ThreeSum.LightScaleArray

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Constructing the positional one-hot coefficient arrays

The program reads one map occurrence per block. It copies both symbol rows
of that map and multiplies them by the block's radix power. The powers are
built internally. All original map and occurrence data are preserved.
-/

namespace ThreeSum.LightBlockCoefficients
open _root_.ThreeSum.LightBlockCoefficients


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}















theorem row_end_le {J L j : ℕ} (hj : j < J) : j*L+L ≤ J*L := by
  calc
    j*L+L = (j+1)*L := by ring
    _ ≤ J*L := Nat.mul_le_mul_right L (by omega)

theorem map_end_le {M L s : ℕ} (hs : s < M) : 2*L*s+L+L ≤ 2*L*M := by
  calc
    2*L*s+L+L = 2*L*(s+1) := by ring
    _ ≤ 2*L*M := Nat.mul_le_mul_left (2*L) (by omega)









end ThreeSum.LightBlockCoefficients

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBlockCoefficients
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000
set_option linter.deprecated false
set_option linter.unusedSimpArgs false
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.meets__implementation_6393abc339 {pMain pPowers pScale : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.body pPowers pScale))
    (hpowers : P[pPowers]? = some _root_.ThreeSum1960614.Machine.Light.powTableBody)
    (hscale : P[pScale]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightScaleArray.body)
    {μ : ℕ → ℤ} {J L p occ maps dst0 dst1 work U M d : ℕ}
    (sel : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hocc : occ+J ≤ dst0) (hmaps : maps+2*L*M ≤ dst0)
    (hdst0 : dst0+J*L ≤ dst1) (hdst1 : dst1+J*L ≤ work)
    (hspace : work+(J+1) ≤ lim.space)
    (hword : (_root_.ThreeSum.LightBlockCoefficients.word J p U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [J,L,p,occ,maps,dst0,dst1,work] μ (_root_.ThreeSum.LightBlockCoefficients.time J L)
      (fun _ ν => _root_.ThreeSum.LightBlockCoefficients.Rows ν dst0 dst1 L p sel w0 w1 J ∧
        _root_.ThreeSum1960614.Machine.Light.Kept μ ν dst0 ∧ _root_.ThreeSum.LightBlockCoefficients.Powers ν work J p) := by
  have hpw : ∀ i ≤ J+1, ((p^i : ℕ) : ℤ) ≤ lim.word := by
    intro i hi
    have hh : p^i ≤ _root_.ThreeSum.LightBlockCoefficients.word J p U :=
      (Nat.pow_le_pow_right hp hi).trans (Nat.le_mul_of_pos_right _ (by omega))
    exact (by exact_mod_cast hh : ((p^i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
  have hpb : (p : ℤ) ≤ lim.word := by simpa using hpw 1 (by omega)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.body _root_.ThreeSum.LightBlockCoefficients.time
  have hpCall := _root_.ThreeSum1960614.Machine.Light.powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := J+1) (b := p) hpowers hw hspace hpw
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hpCall _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hpCall ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.powTableTime, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightScaleArray.time]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.Light.powTableTime, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightScaleArray.time] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.Light.powTableTime, _root_.ThreeSum.LightBlockCoefficients.roundTime, _root_.ThreeSum.LightScaleArray.time] <;> omega)
     on_goal -1 => (rintro rPow ν₀ ⟨hpow, hkeep₀⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.Inv μ J L p occ maps dst0 dst1 work sel w0 w1)
    J (_root_.ThreeSum.LightBlockCoefficients.roundTime L) ?start ?round ?done ?bound (hT := by (first
                                                                                                 | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                                                     first
                                                                                                     | omega
                                                                                                     | (ring_nf; omega))
                                                                                                 | omega
                                                                                                 |
                                                                                                   (simp [] <;>
                                                                                                       first
                                                                                                       | omega
                                                                                                       | (ring_nf; omega))))
  case start =>
    refine ⟨0,0,0,0,0,ν₀,?_,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      change _root_.Light.frame [(J : ℤ),L,p,occ,maps,dst0,dst1,work,0] =
        _root_.Light.frame ([(J : ℤ),L,p,occ,maps,dst0,dst1,work,0] ++ [0,0,0,0,0])
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 5).symm
    · intro a ha
      omega
    · intro a ha
      exact hkeep₀ a (Or.inl (by omega))
    · intro i hi
      have hh := hpow i (by simp; omega)
      simpa only [_root_.ThreeSum1960614.Machine.Light.getElem_powList] using hh
  case round =>
    rintro j _ hj _ ⟨s,a,b,r0,r1,ν,rfl,hrows,hkept,hpows⟩
    have hs := hsel j hj
    have hme := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.map_end_le (L := L) hs
    have hre := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.row_end_le (L := L) hj
    have htwo : 2*L ≤ lim.space :=
      (Nat.le_mul_of_pos_right (2*L) (by omega : 0 < M)).trans (by omega)
    have hprod : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      have hh : 2*L*sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : 2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : 0 ≤ 2*(L : ℤ)*(sel j : ℤ) := by positivity
    have haddrWord : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ) ≤ lim.word := by
      have hh : maps+2*L*sel j ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ) ≤ lim.space).trans hw
    have haddrEndWord : (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ lim.word := by
      have hh : maps+2*L*sel j+L+L ≤ lim.space := by omega
      exact (by exact_mod_cast hh :
        (maps : ℤ)+2*(L : ℤ)*(sel j : ℤ)+(L : ℤ)+(L : ℤ) ≤ lim.space).trans hw
    have hrowProd : (j : ℤ)*(L : ℤ) ≤ lim.word := by
      have hh : j*L ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ)*(L : ℤ) ≤ lim.space).trans hw
    have hrowNonneg : 0 ≤ (j : ℤ)*(L : ℤ) := by positivity
    have hselection : ν (occ+j) = (sel j : ℤ) :=
      (hkept _ (by omega)).trans (hselRead j hj)
    have hpower := hpows j (by omega)
    have hread0' : ∀ i < L, ν (maps+2*L*sel j+i) = (w0 (sel j) i : ℤ) := by
      intro i hi
      exact (hkept _ (by omega)).trans (hread0 _ hs i hi)
    have hread1' : ∀ i < L, ν (maps+2*L*sel j+L+i) = (w1 (sel j) i : ℤ) := by
      intro i hi
      exact (hkept _ (by omega)).trans (hread1 _ hs i hi)
    have hv0 : ∀ i < L, |(p^j : ℕ)*ν (maps+2*L*sel j+i)| ≤ lim.word := by
      intro i hi
      rw [hread0' i hi]
      have hh : p^j*w0 (sel j) i ≤ _root_.ThreeSum.LightBlockCoefficients.word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega))
          ((hbound0 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p^j*w0 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p^j*w0 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Int.abs_natCast] using hz
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.roundBody _root_.ThreeSum.LightBlockCoefficients.roundTime
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (maps + 2 * L * sel j : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hselection, _root_.ThreeSum.LightScaleArray.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hselection, _root_.ThreeSum.LightScaleArray.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hselection, _root_.ThreeSum.LightScaleArray.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (dst0 + j * L : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightScaleArray.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightScaleArray.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightScaleArray.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (dst1 + j * L : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightScaleArray.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightScaleArray.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightScaleArray.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hcall0 := _root_.ThreeSum1960614.Machine.ThreeSum.LightScaleArray.meets (d := d+1) (src := maps+2*L*sel j)
      (dst := dst0+j*L) (n := L) (c := (p^j : ℕ)) hscale hw (by omega) (by omega)
      (Or.inr (Or.inl (by omega))) hv0
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall0 _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall0 ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpower, _root_.ThreeSum.LightScaleArray.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hpower, _root_.ThreeSum.LightScaleArray.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpower, _root_.ThreeSum.LightScaleArray.time] <;> omega)
       on_goal -1 => (rintro q0 ν₁ ⟨hout0, hkeep0⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    have hpower₁ : ν₁ (work+j) = ((p^j : ℕ) : ℤ) :=
      (hkeep0 _ (Or.inr (by omega))).trans hpower
    have hread1'' : ∀ i < L, ν₁ (maps+2*L*sel j+L+i) = (w1 (sel j) i : ℤ) := by
      intro i hi
      exact (hkeep0 _ (Or.inl (by omega))).trans (hread1' i hi)
    have hv1 : ∀ i < L, |(p^j : ℕ)*ν₁ (maps+2*L*sel j+L+i)| ≤ lim.word := by
      intro i hi
      rw [hread1'' i hi]
      have hh : p^j*w1 (sel j) i ≤ _root_.ThreeSum.LightBlockCoefficients.word J p U :=
        Nat.mul_le_mul (Nat.pow_le_pow_right hp (by omega))
          ((hbound1 _ hs i hi).trans (Nat.le_succ U))
      have hz : (((p^j*w1 (sel j) i : ℕ) : ℤ)) ≤ lim.word :=
        (by exact_mod_cast hh : ((p^j*w1 (sel j) i : ℕ) : ℤ) ≤ (word J p U : ℤ)).trans hword
      simpa only [Nat.cast_mul,abs_mul,abs_of_nonneg (Int.natCast_nonneg _),Int.abs_natCast] using hz
    have hcall1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightScaleArray.meets (d := d+1) (src := maps+2*L*sel j+L)
      (dst := dst1+j*L) (n := L) (c := (p^j : ℕ)) hscale hw (by omega) (by omega)
      (Or.inr (Or.inl (by omega))) hv1
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hcall1 _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hcall1 ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hpower₁, _root_.ThreeSum.LightScaleArray.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hpower₁, _root_.ThreeSum.LightScaleArray.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hpower₁, _root_.ThreeSum.LightScaleArray.time] <;> omega)
       on_goal -1 => (rintro q1 ν₂ ⟨hout1, hkeep1⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,((maps+2*L*sel j : ℕ) : ℤ),((dst0+j*L : ℕ) : ℤ),
      ((dst1+j*L : ℕ) : ℤ),q0,q1,ν₂,?_,?_,?_,?_⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
    · intro a ha i hi
      by_cases haj : a = j
      · subst a
        constructor
        · rw [hkeep1 _ (Or.inl (by omega)),hout0 i hi,hread0' i hi,Nat.cast_mul]
        · simpa only [Nat.cast_mul] using (hout1 i hi).trans (by rw [hread1'' i hi])
      · have hal : a < j := by omega
        have he : a*L+i < j*L := by
          have hh := _root_.ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.row_end_le (L := L) hal
          omega
        constructor
        · exact (hkeep1 _ (Or.inl (by omega))).trans
            ((hkeep0 _ (Or.inl (by omega))).trans (hrows a hal i hi).1)
        · exact (hkeep1 _ (Or.inl (by omega))).trans
            ((hkeep0 _ (Or.inr (by omega))).trans (hrows a hal i hi).2)
    · intro a ha
      exact (hkeep1 _ (Or.inl (by omega))).trans
        ((hkeep0 _ (Or.inl (by omega))).trans (hkept a ha))
    · intro a ha
      exact (hkeep1 _ (Or.inr (by omega))).trans
        ((hkeep0 _ (Or.inr (by omega))).trans (hpows a ha))
  case done =>
    rintro _ _ ⟨s,a,b,r0,r1,ν,rfl,hrows,hkept,hpows⟩
    exact ⟨hrows,hkept,hpows⟩
  case bound =>
    rintro j _ hj _ ⟨s,a,b,r0,r1,ν,rfl,_,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
       (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
       simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.meets__implementation_6393abc339) := (@ThreeSum1960614.Machine.ThreeSum.LightBlockCoefficients.meets__implementation_6393abc339)

#print axioms solution
