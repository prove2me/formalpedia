-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightRadixRows.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:32:48.445983+00:00
-- url     : https://prove2.me/submissions/5daf1c23-6c99-43ff-b582-26d54c690595

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Field.ZMod
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
import Mathlib.Data.Bool.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Int.ModEq
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.List.MinMax
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.OfFn
import Mathlib.Data.List.Pi
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.Nat.Choose.Basic
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
import Mathlib.Logic.Function.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Push
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs
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
import Theorems.Thm_Light_seg_append

private theorem platform_seg_append_42cd071063 {μ : ℕ → ℤ} {a : ℕ} {l₁ l₂ : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (l₁ ++ l₂) ↔ _root_.ThreeSum1960614.Machine.Light.Seg μ a l₁ ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + l₁.length) l₂ := by
  exact _root_.Light.seg_append

@[simp] private theorem platform_seg_nil_42cd071063 (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightArray
end ThreeSum.LightArray
namespace ThreeSum.LightRadixRows
end ThreeSum.LightRadixRows
namespace ThreeSum.LightReportingAffine
end ThreeSum.LightReportingAffine
namespace ThreeSum.RadixKeyLists
end ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightArray
end ThreeSum1960614.Machine.ThreeSum.LightArray
namespace ThreeSum1960614.Machine.ThreeSum.LightRadixRows
end ThreeSum1960614.Machine.ThreeSum.LightRadixRows
namespace ThreeSum1960614.Machine.ThreeSum.LightReportingAffine
end ThreeSum1960614.Machine.ThreeSum.LightReportingAffine
namespace ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
end ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Exact product-list semantics for global radix-key construction

The key list retains every local occurrence, even when several records have
the same integer key. Each stage prepends one local record and computes its
positional hash. This is the order used by the concrete row constructor.
-/

namespace ThreeSum.RadixKeyLists
open _root_.ThreeSum.RadixKeyLists


variable {α β : Type*}





theorem step_length (p : ℤ) (base prev : List ℤ) :
    (_root_.ThreeSum.RadixKeyLists.step p base prev).length=base.length*prev.length :=
  _root_.ThreeSum.RadixKeyLists.flatMap_length_uniform base _ prev.length (by simp)

theorem step_take_succ (p : ℤ) (base prev : List ℤ) {i : ℕ} (hi : i < base.length) :
    _root_.ThreeSum.RadixKeyLists.step p (base.take (i+1)) prev = _root_.ThreeSum.RadixKeyLists.step p (base.take i) prev ++
      prev.map (fun y => base[i]+p*y) := by
  rw [List.take_succ_eq_append_getElem hi]
  simp only [_root_.ThreeSum.RadixKeyLists.step,List.flatMap_append,List.flatMap_singleton]

















end ThreeSum.RadixKeyLists

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



theorem SameOn.refl : _root_.ThreeSum1960614.Machine.Light.SameOn K μ μ := fun _ _ => rfl









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









@[simp] theorem Seg.nil : _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := fun i h => absurd h (by simp)















/-- A segment only depends on its own cells. -/
theorem Seg.congr (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) (he : ∀ i < l.length, μ' (a + i) = μ (a + i)) : _root_.ThreeSum1960614.Machine.Light.Seg μ' a l :=
  fun i hi => by rw [he i hi, h i hi]











theorem SameOutside.refl : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ a n := _root_.ThreeSum1960614.Machine.Light.SameOn.refl









/-- A segment that does not meet the region is kept. -/
theorem Seg.of_sameOutside (h : _root_.ThreeSum1960614.Machine.Light.Seg μ b l) (hs : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n)
    (hd : b + l.length ≤ a ∨ a + n ≤ b) : _root_.ThreeSum1960614.Machine.Light.Seg μ' b l :=
  h.congr fun i hi => hs _ (by omega)































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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightRadixRows
open _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.RadixKeyLists
open _root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists
set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightRadixRows.meets__implementation_90e28be894 {pMain pAffine srcBase srcPrev dst p U V : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.body pAffine))
    (haffine : P[pAffine]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.body)
    (base prev : List ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hbaseEnd : srcBase+base.length ≤ dst) (hprevEnd : srcPrev+prev.length ≤ dst)
    (hspace : dst+base.length*prev.length ≤ lim.space)
    (hword : (_root_.ThreeSum.LightRadixRows.word p U V : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hbaseRead : _root_.ThreeSum1960614.Machine.Light.Seg μ srcBase base) (hprevRead : _root_.ThreeSum1960614.Machine.Light.Seg μ srcPrev prev)
    (hbaseBound : ∀ x ∈ base, |x| ≤ (U : ℤ))
    (hprevBound : ∀ y ∈ prev, |y| ≤ (V : ℤ)) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [srcBase,srcPrev,dst,base.length,prev.length,p] μ
      (_root_.ThreeSum.LightRadixRows.time base.length prev.length)
      (fun _ ν => _root_.ThreeSum1960614.Machine.Light.Seg ν dst (_root_.ThreeSum.RadixKeyLists.step (p : ℤ) base prev) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ ν dst (base.length*prev.length)) := by
  have hbudget (n : ℕ) (hn : n ≤ _root_.ThreeSum.LightRadixRows.word p U V) : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hn).trans hword
  have hpWord := hbudget p (by unfold _root_.ThreeSum.LightRadixRows.word; omega)
  have hsumWord := hbudget (U+p*V) (by unfold _root_.ThreeSum.LightRadixRows.word; omega)
  have hmulWord := hbudget (p*V) (by unfold _root_.ThreeSum.LightRadixRows.word; omega)
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.body _root_.ThreeSum.LightRadixRows.time
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightRadixRows.Inv μ srcBase srcPrev dst p base prev) base.length
    (_root_.ThreeSum.LightReportingAffine.time prev.length+75) ?start ?round ?done ?bound
    (hT := by (first
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
    refine ⟨0,μ,?_,?_,_root_.ThreeSum1960614.Machine.Light.SameOutside.refl⟩
    · simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
      change _root_.Light.frame [(srcBase : ℤ),srcPrev,dst,base.length,prev.length,p,0] =
        _root_.Light.frame ([(srcBase : ℤ),srcPrev,dst,base.length,prev.length,p,0] ++ [0])
      exact (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 1).symm
    · simp [_root_.ThreeSum.RadixKeyLists.step]
  case round =>
    rintro j _ hj _ ⟨r,ν,rfl,hout,hkeep⟩
    have hend : j*prev.length+prev.length ≤ base.length*prev.length := by
      calc
        j*prev.length+prev.length = (j+1)*prev.length := by ring
        _ ≤ base.length*prev.length := Nat.mul_le_mul_right prev.length (by omega)
    have hjProd : (j : ℤ)*(prev.length : ℤ) ≤ lim.word := by
      have hh : j*prev.length ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (j : ℤ)*(prev.length : ℤ) ≤ lim.space).trans hw
    have hrowAddr : (dst : ℤ)+(j : ℤ)*(prev.length : ℤ) ≤ lim.word := by
      have hh : dst+j*prev.length ≤ lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ)+(j : ℤ)*(prev.length : ℤ) ≤ lim.space).trans hw
    have hreadBase : ν (srcBase+j)=base[j] :=
      (hkeep _ (Or.inl (by omega))).trans (hbaseRead j hj)
    have hreadPrev (i : ℕ) (hi : i < prev.length) : ν (srcPrev+i)=prev[i] :=
      (hkeep _ (Or.inl (by omega))).trans (hprevRead i hi)
    have hkey := hbaseBound _ (List.getElem_mem hj)
    have hmul : ∀ i < prev.length, |(p : ℤ)*ν (srcPrev+i)| ≤ lim.word := by
      intro i hi
      rw [hreadPrev i hi,abs_mul,Int.abs_natCast]
      exact (mul_le_mul_of_nonneg_left (hprevBound _ (List.getElem_mem hi))
        (Int.natCast_nonneg _)).trans (by simpa only [Nat.cast_mul] using hmulWord)
    have hsum : ∀ i < prev.length, |base[j]+(p : ℤ)*ν (srcPrev+i)| ≤ lim.word := by
      intro i hi
      have hv : |(p : ℤ)*ν (srcPrev+i)| ≤ (p : ℤ)*V := by
        rw [hreadPrev i hi,abs_mul,Int.abs_natCast]
        exact mul_le_mul_of_nonneg_left (hprevBound _ (List.getElem_mem hi))
          (Int.natCast_nonneg _)
      exact (abs_add_le _ _).trans ((add_le_add hkey hv).trans
        (by simpa only [Nat.cast_add,Nat.cast_mul] using hsumWord))
    have hc := _root_.ThreeSum1960614.Machine.ThreeSum.LightReportingAffine.meets (d := d+1) (src := srcPrev)
      (dst := dst+j*prev.length) (n := prev.length) (b := base[j]) (c := (p : ℤ))
      haffine hw (by omega) (by omega) (Or.inr (Or.inl (by omega))) hmul hsum
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
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hreadBase, _root_.ThreeSum.LightReportingAffine.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hreadBase, _root_.ThreeSum.LightReportingAffine.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hreadBase, _root_.ThreeSum.LightReportingAffine.time] <;> omega)
       on_goal -1 => (rintro result ν₁ ⟨hrow, hrowKeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    refine ⟨by simp,result,ν₁,by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_⟩
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.step_take_succ _ _ _ hj]
      have hlen : (_root_.ThreeSum.RadixKeyLists.step (p : ℤ) (base.take j) prev).length=j*prev.length := by
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.RadixKeyLists.step_length,List.length_take,min_eq_left (Nat.le_of_lt hj)]
      apply platform_seg_append_42cd071063.mpr
      constructor
      · exact hout.of_sameOutside hrowKeep (Or.inl (by rw [hlen]))
      · rw [hlen]
        intro i hi
        have hi' : i < prev.length := by simpa only [List.length_map] using hi
        rw [List.getElem_map,hrow i hi',hreadPrev i hi']
    · intro a ha
      exact (hrowKeep a (by omega)).trans (hkeep a ha)
  case done =>
    rintro _ _ ⟨r,ν,rfl,hout,hkeep⟩
    exact ⟨by simpa only [List.take_length] using hout,hkeep⟩
  case bound =>
    rintro j _ hj _ ⟨r,ν,rfl,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightRadixRows.meets__implementation_90e28be894) := (@ThreeSum1960614.Machine.ThreeSum.LightRadixRows.meets__implementation_90e28be894)

#print axioms solution
