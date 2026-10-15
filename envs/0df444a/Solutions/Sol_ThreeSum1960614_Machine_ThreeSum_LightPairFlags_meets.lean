-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightPairFlags.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:53.668678+00:00
-- url     : https://prove2.me/submissions/a43c3c82-af95-4b5b-83d0-916f1668e36c

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightBooleanDot_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSmallDivide_meets
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightTrimTest_meets

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightPairFlags
end ThreeSum.LightPairFlags
namespace ThreeSum.LightTrimTest
end ThreeSum.LightTrimTest
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightPairFlags
end ThreeSum1960614.Machine.ThreeSum.LightPairFlags
namespace ThreeSum1960614.Machine.ThreeSum.LightTrimTest
end ThreeSum1960614.Machine.ThreeSum.LightTrimTest
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

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





































theorem SameOutside.refl : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ a n := _root_.ThreeSum1960614.Machine.Light.SameOn.refl



/-- Writing inside the region. -/
theorem SameOutside.update (h : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n) (hb : a ≤ b ∧ b < a + n) (x : ℤ) :
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ (Function.update μ' b x) a n := fun c hc => by
  rw [Function.update_of_ne (by omega)]; exact h c hc





































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

/-! # The exact local retained-edge test -/

namespace ThreeSum.LightTrimTest
open _root_.ThreeSum.LightTrimTest


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light



theorem flag_le (overlap leftCount rightCount cap : ℕ) : _root_.ThreeSum.LightTrimTest.flag overlap leftCount rightCount cap ≤ 1 := by
  unfold _root_.ThreeSum.LightTrimTest.flag
  split <;> omega







variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}





end ThreeSum.LightTrimTest

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightPairFlags
open _root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1500000
set_option maxRecDepth 5000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightPairFlags.meets__implementation_e84168244a {pMain pDivide pDot pTrim : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.body pDivide pDot pTrim))
    (hdivide : P[pDivide]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.body)
    (hdot : P[pDot]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.body)
    (htrim : P[pTrim]? = some _root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest.body)
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ dst) (hleft : leftPtr+n ≤ dst) (hright : rightPtr+n ≤ dst)
    (hleftHist : leftHist+p ≤ dst) (hrightHist : rightHist+p ≤ dst)
    (hspace : dst+2*(n*n) ≤ lim.space) (hword : (_root_.ThreeSum.LightPairFlags.word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap] μ (_root_.ThreeSum.LightPairFlags.time L n)
      (fun _ μ' =>
        (∀ i < n*n, μ' (dst+i) = (_root_.ThreeSum.LightPairFlags.pairKey n p left right i : ℤ)) ∧
        (∀ i < n*n, μ' (dst+n*n+i) = (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst (2*(n*n))) := by
  have hbudget (x : ℕ) (hx : x ≤ _root_.ThreeSum.LightPairFlags.word L n p cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hnWord := hbudget n (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
  have heWord := hbudget (n*n) (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
  have h1Word := hbudget 1 (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
  have heWordZ : (n : ℤ)*(n : ℤ) ≤ lim.word := by exact_mod_cast heWord
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.body _root_.ThreeSum.LightPairFlags.time
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (dst + n * n : ℕ) ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightPairFlags.word]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightPairFlags.word] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightPairFlags.word] <;> omega)
     try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (_root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.Inv μ bits left right leftCount rightCount
    bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap) (n*n) (_root_.ThreeSum.LightPairFlags.roundTime L n) ?_ ?_ ?_ ?_
    (hT := by (first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time] <;>
                     first
                     | omega
                     | (ring_nf; omega))))
  · refine ⟨0,0,0,0,0,0,μ,?_,?_,?_,_root_.ThreeSum1960614.Machine.Light.SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : _root_.ThreeSum1960614.Machine.Light.State))
        ((_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal _ _ _).trans (_root_.ThreeSum1960614.Machine.Light.frame_append_zeros _ 6).symm)
    · intro j hj; omega
    · intro j hj; omega
  · rintro i _ hi _ ⟨a,b,c,e,f,g,μ',rfl,writtenKeys,writtenFlags,kept⟩
    have hq : i/n < n := (Nat.div_lt_iff_lt_mul hn).mpr hi
    have hr : i%n < n := Nat.mod_lt i hn
    have hqmul : i/n*n ≤ i := Nat.div_mul_le_self i n
    have hqr : i%n+i/n*n = i := by simpa only [Nat.mul_comm] using Nat.mod_add_div i n
    have hdivWord : ((i+n+2 : ℕ) : ℤ) ≤ lim.word :=
      hbudget _ (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
    have hdivTime : _root_.ThreeSum.LightSmallDivide.time i n ≤ 20*n+40 := by unfold _root_.ThreeSum.LightSmallDivide.time; omega
    have hqWord := hbudget (i/n) (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
    have hrWord := hbudget (i%n) (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
    have hqNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ) := by
      rw [← Int.natCast_ediv]
      exact Int.natCast_nonneg _
    have hrem : (i : ℤ)-((i/n : ℕ) : ℤ)*n = ((i%n : ℕ) : ℤ) := by exact_mod_cast (by omega : i-i/n*n=i%n)
    have hqmulZ : ((i/n : ℕ) : ℤ)*(n : ℤ) ≤ lim.word := by
      have hh : i/n*n ≤ _root_.ThreeSum.LightPairFlags.word L n p cap := by unfold _root_.ThreeSum.LightPairFlags.word; omega
      exact (by exact_mod_cast hh : ((i/n : ℕ) : ℤ)*(n : ℤ) ≤ (word L n p cap : ℤ)).trans hword
    have hqmulInt : (i : ℤ)/(n : ℤ)*n ≤ lim.word := by
      simpa only [Int.natCast_ediv] using hqmulZ
    have hqmulNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ)*n := by
      rw [← Int.natCast_ediv,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hremInt : (i : ℤ)-(i : ℤ)/(n : ℤ)*n = ((i%n : ℕ) : ℤ) := by
      simpa only [Int.natCast_ediv] using hrem
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightPairFlags.roundBody
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := i) (b := n) hdivide μ' hdivWord) _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.ThreeSum.LightSmallDivide.meets (d := d + 1) (a := i) (b := n) hdivide μ' hdivWord) ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
       on_goal -1 => (rintro qval μ₁ ⟨hqval, hmem₁⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₁
    subst qval
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (i % n : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hremInt, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hremInt, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hremInt, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hqL : (i/n+1)*L ≤ n*L := Nat.mul_le_mul_right L (by omega)
    have hrL : (i%n+1)*L ≤ n*L := Nat.mul_le_mul_right L (by omega)
    have hqRow : bitPtr+i/n*L+L ≤ dst := by nlinarith
    have hrRow : bitPtr+i%n*L+L ≤ dst := by nlinarith
    have hqRead : ∀ j < L, μ' (bitPtr+i/n*L+j) = (bits (i/n) j : ℤ) := by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hq j hj
    have hrRead : ∀ j < L, μ' (bitPtr+i%n*L+j) = (bits (i%n) j : ℤ) := by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hr j hj
    have hqLMulWord : (((i/n)*L : ℕ) : ℤ) ≤ lim.word := by
      have hh : (i/n)*L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hrLMulWord : (((i%n)*L : ℕ) : ℤ) ≤ lim.word := by
      have hh : (i%n)*L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hqLInt : (i : ℤ)/(n : ℤ)*L ≤ lim.word := by
      simpa only [Nat.cast_mul,Int.natCast_ediv] using hqLMulWord
    have hqLNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ)*L := by
      rw [← Int.natCast_ediv,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hrLInt : (i : ℤ)%(n : ℤ)*L ≤ lim.word := by
      simpa only [Nat.cast_mul,Int.natCast_emod] using hrLMulWord
    have hrLNonneg : (0 : ℤ) ≤ (i : ℤ)%(n : ℤ)*L := by
      rw [← Int.natCast_emod,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hqa : ((bitPtr : ℤ)+((i/n : ℕ) : ℤ)*L).toNat = bitPtr+i/n*L := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hra : ((bitPtr : ℤ)+((i%n : ℕ) : ℤ)*L).toNat = bitPtr+i%n*L := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hqaInt : ((bitPtr : ℤ)+(i : ℤ)/(n : ℤ)*L).toNat = bitPtr+i/n*L := by
      simpa only [Int.natCast_ediv] using hqa
    have hraInt : ((bitPtr : ℤ)+(i : ℤ)%(n : ℤ)*L).toNat = bitPtr+i%n*L := by
      simpa only [Int.natCast_emod] using hra
    have hqaBound : (bitPtr : ℤ)+(i : ℤ)/(n : ℤ)*L ≤ lim.word := by
      have hh : ((bitPtr+i/n*L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr+i/n*L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add,Nat.cast_mul,Int.natCast_ediv] using hh
    have hraBound : (bitPtr : ℤ)+(i : ℤ)%(n : ℤ)*L ≤ lim.word := by
      have hh : ((bitPtr+i%n*L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr+i%n*L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add,Nat.cast_mul,Int.natCast_emod] using hh
    have hdotCall := _root_.ThreeSum1960614.Machine.ThreeSum.LightBooleanDot.meets (d := d+1) (μ := μ')
      (srcA := bitPtr+i/n*L) (srcB := bitPtr+i%n*L) (n := L)
      hdot (bits (i/n)) (bits (i%n)) hw (by omega) (by omega) hqRead hrRead
      (hbitsValue _ hq) (hbitsValue _ hr) h1Word
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (hdotCall _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen hdotCall ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hqa, hra, hqaInt, hraInt, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hqa, hra, hqaInt, hraInt, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hqa, hra, hqaInt, hraInt, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
       on_goal -1 => (rintro overlap μ₂ ⟨hoverlap, hmem₂⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₂
    have hlr : μ' (leftPtr+i/n) = (left (i/n) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hleftRead _ hq)
    have hrr : μ' (rightPtr+i%n) = (right (i%n) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hrightRead _ hr)
    have hlLt := hleftLt _ hq
    have hrLt := hrightLt _ hr
    have hlAddr : ((leftPtr : ℤ)+(i : ℤ)/(n : ℤ)).toNat = leftPtr+i/n := by
      rw [← Int.natCast_ediv,← Nat.cast_add,Int.toNat_natCast]
    have hrAddr : ((rightPtr : ℤ)+(i : ℤ)%(n : ℤ)).toNat = rightPtr+i%n := by
      rw [← Int.natCast_emod,← Nat.cast_add,Int.toNat_natCast]
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (left (i / n) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hlAddr, hlr, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hlAddr, hlr, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hlAddr, hlr, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (right (i % n) : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hrAddr, hrr, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hrAddr, hrr, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hrAddr, hrr, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    have hlc : μ' (leftHist+left (i/n)) = (leftCount (left (i/n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hleftCount _ hlLt)
    have hrc : μ' (rightHist+right (i%n)) = (rightCount (right (i%n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hrightCount _ hrLt)
    have hcL := hleftBound _ hlLt
    have hcR := hrightBound _ hrLt
    have ht := _root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest.meets (d := d+1)
      (x := _root_.ThreeSum.LightBooleanDot.dot (bits (i/n)) (bits (i%n)) L)
      (l := leftCount (left (i/n))) (r := rightCount (right (i%n))) (b := cap)
      htrim μ' h1Word (hbudget _ (by unfold _root_.ThreeSum.LightPairFlags.word; omega))
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
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (ht _ (by omega)) ?_ ?_ ?_ ?_
       | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ht ?_ ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hoverlap, hlc, hrc, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hoverlap, hlc, hrc, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 => omega
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hoverlap, hlc, hrc, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
       on_goal -1 => (rintro flag μ₃ ⟨hflag, hmem₃⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
    subst μ₃
    have hk : _root_.ThreeSum.LightPairFlags.pairKey n p left right i < p*p := by
      unfold _root_.ThreeSum.LightPairFlags.pairKey
      nlinarith
    have hkWord := hbudget (_root_.ThreeSum.LightPairFlags.pairKey n p left right i) (by unfold _root_.ThreeSum.LightPairFlags.word; omega)
    have hkWordZ : (left (i/n) : ℤ)*p+right (i%n) ≤ lim.word := by
      simpa only [_root_.ThreeSum.LightPairFlags.pairKey,Nat.cast_add,Nat.cast_mul] using hkWord
    have hprodWord : ((left (i/n)*p : ℕ) : ℤ) ≤ lim.word := by
      have hh : left (i/n)*p ≤ _root_.ThreeSum.LightPairFlags.word L n p cap := by unfold _root_.ThreeSum.LightPairFlags.pairKey at hk; unfold _root_.ThreeSum.LightPairFlags.word; omega
      exact (Int.ofNat_le.mpr hh).trans hword
    have hflag' : flag = (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i : ℤ) := hflag
    have hf : _root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i ≤ 1 := _root_.ThreeSum1960614.Machine.ThreeSum.LightTrimTest.flag_le ..
    have hfZ : (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i : ℤ) ≤ lim.word := by omega
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + i) (_root_.ThreeSum.LightPairFlags.pairKey n p left right i : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightPairFlags.pairKey, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [_root_.ThreeSum.LightPairFlags.pairKey, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightPairFlags.pairKey, _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
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
       refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (dst + n * n + i) (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i : ℕ) ?_ ?_ ?_
       on_goal -1 =>
         first
         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hflag', _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time]
             first
             | omega
             | (ring_nf; omega))
         | omega
         |
           (simp [hflag', _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;>
               first
               | omega
               | (ring_nf; omega))
       on_goal -1 =>
         ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
           (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
           simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflag', _root_.ThreeSum.LightPairFlags.roundTime, _root_.ThreeSum.LightBooleanDot.time, _root_.ThreeSum.LightTrimTest.time, _root_.ThreeSum.LightSmallDivide.time] <;> omega)
       try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
    refine ⟨by simp,(i/n : ℕ),i%n,overlap,left (i/n),right (i%n),flag,
      Function.update (Function.update μ' (dst+i) (_root_.ThreeSum.LightPairFlags.pairKey n p left right i : ℤ))
        (dst+n*n+i) (_root_.ThreeSum.LightPairFlags.pairFlag L n cap bits left right leftCount rightCount i : ℤ),
      by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact writtenKeys j hj
      · rw [Function.update_of_ne (by omega),Function.update_self]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact writtenFlags j hj
      · rw [Function.update_self]
    · exact (kept.update ⟨by omega,by omega⟩ _).update ⟨by omega,by omega⟩ _
  · rintro _ _ ⟨a,b,c,e,f,g,μ',rfl,writtenKeys,writtenFlags,kept⟩
    exact ⟨writtenKeys,writtenFlags,kept⟩
  · rintro i _ _ _ ⟨a,b,c,e,f,g,μ',rfl,_,_,_⟩
    (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightPairFlags.meets__implementation_e84168244a) := (@ThreeSum1960614.Machine.ThreeSum.LightPairFlags.meets__implementation_e84168244a)

#print axioms solution
