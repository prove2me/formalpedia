-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:47:33.030406+00:00
-- url     : https://prove2.me/submissions/fb8703ed-91f9-4630-84d8-ef2c0f703b20

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle011
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle06
import Lean
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Algebra.Order.BigOperators.Group.Multiset
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Int
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.Dedup
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
import Theorems.Thm_Light_seg_cons

private theorem platform_seg_cons_3ed3864a2d {μ : ℕ → ℤ} {a : ℕ} {x : ℤ} {l : List ℤ} :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a (x :: l) ↔ μ a = x ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ (a + 1) l := by
  exact _root_.Light.seg_cons

@[simp] private theorem platform_seg_nil_3ed3864a2d (μ : ℕ → ℤ) (a : ℕ) :
    _root_.ThreeSum1960614.Machine.Light.Seg μ a [] := by
  intro i h
  exact (Nat.not_lt_zero i h).elim


namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightNormalize
end ThreeSum.LightNormalize
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightNormalize
end ThreeSum1960614.Machine.ThreeSum.LightNormalize
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















theorem Ends.ite {σ T c s₁ s₂} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (T' : ℕ) (hs : c.Safe lim σ)
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ T' Q) (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ T' Q)
    (hT : c.cost + 1 + T' ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q := by
  by_cases hv : c.Holds σ
  · obtain ⟨σ', k, he, hk, hq⟩ := h₁ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteTrue hs hv he, by omega, hq⟩
  · obtain ⟨σ', k, he, hk, hq⟩ := h₂ hv
    exact ⟨σ', _, _root_.ThreeSum1960614.Machine.Light.Exec.iteFalse hs hv he, by omega, hq⟩













/-! ## Notation for writing programs

Not trusted: a theorem about a program does not depend on how the program was typed in. -/


















/-! ## Simplification -/

attribute [simp] _root_.ThreeSum1960614.Machine.Light.Expr.val _root_.ThreeSum1960614.Machine.Light.Expr.cost _root_.ThreeSum1960614.Machine.Light.Expr.Safe _root_.Light.Op.eval _root_.ThreeSum1960614.Machine.Light.Cond.Holds _root_.ThreeSum1960614.Machine.Light.Cond.cost _root_.ThreeSum1960614.Machine.Light.Cond.Safe _root_.Light.frame







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



























theorem SameOutside.refl : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ a n := _root_.ThreeSum1960614.Machine.Light.SameOn.refl

/-- A larger region may change. -/
theorem SameOutside.mono {a' n' : ℕ} (h : _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a n) (ha : a' ≤ a)
    (hn : a + n ≤ a' + n') :
    _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' a' n' := fun b hb => h b (by omega)







































end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Derived rules: time that is not typed, blocks, counting loops

The rules of this file spare the typing of step counts.  Ends.next gives the first statement its
time and the rest of the program what is left; Ends.setThen, Ends.storeThen and Ends.iteThen do the
same for one assignment, store or branch, and Ends.setLast, Ends.storeLast and Ends.iteLast treat
the last statement of a program.  `Ends.pieceThen` and `Ends.pieceLast` are the two forms for a
piece of the program that has a lemma of its own.  In every rule the main premises come first, then
the side conditions, and last the comparison of times.  The comparison has the default proof
`light_time`, safety conditions have the default proof `light_side`.

A block is a statement without loops and calls.  s.Runs lim σ R says that the block s runs safely
from σ and ends in a state that satisfies R; Ends.block turns this into a fact about time, with the
cost computed. Ends.whileBlock is the rule for a loop whose body is a block.

Stmt.for i hi body is the loop "for i = 0, …, hi - 1 do body".  The rule Ends.for owns the counter:
the safety of the test and of the increment and the number of steps of the loop are settled here,
once. Ends.forMem is the common case in which the body changes no local variable, so that the
invariant speaks about the memory only.  The three parts of every loop rule are called start, round
and done.  A loop rule is told a bound b on the steps of a round; for a round that is a block with
a name, say xRound, this is xRound.blockCost.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## Blocks -/











/-! ## The default proofs -/











/-! ## Rules for blocks -/













/-! ## Sequencing: what is left of the time goes to the rest of the program -/























/-- A branch at the end of the program: both sides get the steps that the test leaves. -/
theorem Ends.iteLast {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {s₁ s₂ : _root_.ThreeSum1960614.Machine.Light.Stmt} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h₁ : c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₁ σ (T - (c.cost + 1)) Q)
    (h₂ : ¬ c.Holds σ → _root_.ThreeSum1960614.Machine.Light.Ends lim P d s₂ σ (T - (c.cost + 1)) Q)
    (hs : c.Safe lim σ := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega))) (hT : c.cost + 1 ≤ T := by (first
                                                                     | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                                                         first
                                                                         | omega
                                                                         | (ring_nf; omega))
                                                                     | omega
                                                                     |
                                                                       (simp [] <;>
                                                                           first
                                                                           | omega
                                                                           | (ring_nf; omega)))) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.ite c s₁ s₂) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.ite _ hs h₁ h₂ (by omega)





/-! ## Loops whose body is a block -/



/-! ## Counting loops -/







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
# Sorting and deduplicating a single already separated color class

The merge-sort implementation and proof are reused unchanged from the
attached upstream `ThreeSumApsp/Lang/Lib/Merge{,Sort}.lean` sources. The new
linear procedure removes adjacent repeats from the sorted output. The
original membership equivalence is retained, which is the witness needed
by the three-color reduction. Duplicates are removed only inside a class.
-/

namespace ThreeSum.LightNormalize
open _root_.ThreeSum.LightNormalize


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}







theorem sorted_head_not_mem {x y : ℤ} {zs : List ℤ}
    (hs : (x::y::zs).Pairwise (· ≤ ·)) (hne : x ≠ y) : x ∉ y::zs := by
  simp only [List.pairwise_cons] at hs
  intro hx
  rcases List.mem_cons.mp hx with hxy | hx
  · exact hne hxy
  · exact hne (le_antisymm (hs.1 y (by simp)) (hs.2.1 x hx))






















end ThreeSum.LightNormalize

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightNormalize
open _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets__implementation_09fb5de387 {pDedup : ℕ}
    (hprog : P[pDedup]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedupBody pDedup))
    (hw : (lim.space : ℤ) ≤ lim.word) (h1 : (1 : ℤ) ≤ lim.word) :
    ∀ (L : List ℤ) (μ : ℕ → ℤ) (src dst d : ℕ),
      L.Pairwise (· ≤ ·) → _root_.ThreeSum1960614.Machine.Light.Seg μ src L → src+L.length ≤ dst →
      dst+L.length ≤ lim.space → d+L.length ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pDedup d [src,L.length,dst] μ (_root_.ThreeSum.LightNormalize.dedupTime L.length)
        (fun r μ' => r = (L.dedup.length : ℤ) ∧ _root_.ThreeSum1960614.Machine.Light.Seg μ' dst L.dedup ∧
          _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst L.length) := by
  intro L
  induction L with
  | nil =>
      intro μ src dst d hs hseg hsep hspace hd
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hprog
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedupBody _root_.ThreeSum.LightNormalize.dedupTime
      refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
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
      exact ⟨rfl,_root_.ThreeSum1960614.Machine.Light.Seg.nil,_root_.ThreeSum1960614.Machine.Light.SameOutside.refl⟩
  | cons x zs ih =>
      intro μ src dst d hs hseg hsep hspace hd
      have hlen : (x::zs).length = zs.length+1 := rfl
      have hzs := hs.tail
      have hsource := (platform_seg_cons_3ed3864a2d.mp hseg).1
      have htail := (platform_seg_cons_3ed3864a2d.mp hseg).2
      have hsmall := (List.dedup_sublist zs).length_le
      have hemit :
          _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.emitBody pDedup) ⟨_root_.Light.frame [src,zs.length+1,dst],μ⟩
            (200*zs.length+180)
            (fun σ => σ.loc 0 = ((x::zs.dedup).length : ℤ) ∧
              _root_.ThreeSum1960614.Machine.Light.Seg σ.mem dst (x::zs.dedup) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ σ.mem dst (zs.length+1)) := by
        unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.emitBody
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen dst x ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsource, _root_.ThreeSum.LightNormalize.dedupTime]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hsource, _root_.ThreeSum.LightNormalize.dedupTime] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsource, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
           try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
        have htail' : _root_.ThreeSum1960614.Machine.Light.Seg (Function.update μ dst x) (src+1) zs := by
          intro i hi
          rw [Function.update_of_ne (by omega)]
          exact htail i hi
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
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((ih (Function.update μ dst x) (src + 1) (dst + 1) (d + 1) hzs htail' (by omega) (by omega) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (ih (Function.update μ dst x) (src + 1) (dst + 1) (d + 1) hzs htail' (by omega) (by omega) (by omega)) ?_ ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNormalize.dedupTime]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [_root_.ThreeSum.LightNormalize.dedupTime] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 => omega
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
           on_goal -1 => (rintro count μ' ⟨hcount, hout, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
        (focus
           ((first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
             repeat
               with_unfolding_none
                 first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
           refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (zs.dedup.length + 1 : ℕ) ?_ ?_ ?_
           on_goal -1 =>
             first
             | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hcount, _root_.ThreeSum.LightNormalize.dedupTime]
                 first
                 | omega
                 | (ring_nf; omega))
             | omega
             |
               (simp [hcount, _root_.ThreeSum.LightNormalize.dedupTime] <;>
                   first
                   | omega
                   | (ring_nf; omega))
           on_goal -1 =>
             ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
               (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
               simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hcount, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
           try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
        refine ⟨by simp,?_,?_⟩
        · rw [platform_seg_cons_3ed3864a2d]
          refine ⟨?_,hout⟩
          change μ' dst = x
          rw [hkeep dst (Or.inl (by omega)),Function.update_self]
        · intro a ha
          change μ' a = μ a
          rw [hkeep a (by omega),Function.update_of_ne (by omega)]
      apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hprog
      unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedupBody _root_.ThreeSum.LightNormalize.dedupTime
      refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
      cases zs with
      | nil =>
          refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun h => False.elim (by simp at h)) (fun _ => ?_)
          simpa using hemit.mono (by (first
                                      | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                          first
                                          | omega
                                          | (ring_nf; omega))
                                      | omega
                                      |
                                        (simp [] <;>
                                            first
                                            | omega
                                            | (ring_nf; omega)))) (fun _ h => h)
      | cons y ys =>
          have hysLen : (y::ys).length = ys.length+1 := rfl
          have hnext : μ (src+1) = y := (platform_seg_cons_3ed3864a2d.mp htail).1
          refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simp at h))
          (focus
             ((first
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
                 | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
             refine _root_.ThreeSum1960614.Machine.Light.Ends.iteIffThen (x = y) (fun hxy => ?_) (fun hxy => ?_) ?_ ?_
             on_goal -1 =>
               first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, hsource, hnext, _root_.ThreeSum.LightNormalize.dedupTime]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [hsource, hnext, _root_.ThreeSum.LightNormalize.dedupTime] <;>
                     first
                     | omega
                     | (ring_nf; omega))
             on_goal -1 =>
               ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                 (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                 simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hsource, hnext, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
             all_goals
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
          · have hdedup : (x::y::ys).dedup = (y::ys).dedup :=
              List.dedup_cons_of_mem (by simp [hxy])
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
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((ih μ (src + 1) dst (d + 1) hzs htail (by omega) (by omega) (by omega)) _ (by omega)) ?_ ?_ ?_ ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (ih μ (src + 1) dst (d + 1) hzs htail (by omega) (by omega) (by omega)) ?_ ?_ ?_ ?_
               on_goal -1 =>
                 first
                 | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightNormalize.dedupTime]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [_root_.ThreeSum.LightNormalize.dedupTime] <;>
                       first
                       | omega
                       | (ring_nf; omega))
               on_goal -1 => omega
               on_goal -1 =>
                 ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
                   (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
                   simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightNormalize.dedupTime] <;> omega)
               on_goal -1 => (rintro count μ' ⟨hcount, hout, hkeep⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
            refine ⟨by simpa [hdedup] using hcount,by simpa [hdedup] using hout,?_⟩
            exact hkeep.mono le_rfl (by simp)
          · have hdedup : (x::y::ys).dedup = x::(y::ys).dedup :=
              List.dedup_cons_of_notMem (_root_.ThreeSum1960614.Machine.ThreeSum.LightNormalize.sorted_head_not_mem hs hxy)
            (focus
               repeat
                 with_unfolding_none
                   first
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
                   | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceThen hemit ?_ ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.pieceLast hemit ?_ ?_
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
               on_goal -1 => rintro σ h)
            (with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_)
            exact ⟨by simpa [hdedup] using h.1,by simpa [hdedup] using h.2.1,h.2.2⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets__implementation_09fb5de387) := (@ThreeSum1960614.Machine.ThreeSum.LightNormalize.dedup_meets__implementation_09fb5de387)

#print axioms solution
