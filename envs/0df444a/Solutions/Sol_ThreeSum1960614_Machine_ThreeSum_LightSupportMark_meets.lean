-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightSupportMark.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:36:23.059376+00:00
-- url     : https://prove2.me/submissions/78300798-eaa9-4709-83a1-dc68f89e8498

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
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle03
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
import Mathlib.Data.Finset.Range
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_pass

namespace Finset
end Finset
namespace Light
end Light
namespace Light.Copy
end Light.Copy
namespace Light.Fill
end Light.Fill
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightSupportMark
end ThreeSum.LightSupportMark
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.Light.Copy
end ThreeSum1960614.Machine.Light.Copy
namespace ThreeSum1960614.Machine.Light.Fill
end ThreeSum1960614.Machine.Light.Fill
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightSupportMark
end ThreeSum1960614.Machine.ThreeSum.LightSupportMark
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



















/-- A store at the end of the program. -/
theorem Ends.storeLast {loc μ : ℕ → ℤ} {T : ℕ} {a e : _root_.ThreeSum1960614.Machine.Light.Expr} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (h : Q ⟨loc, Function.update μ (a.val ⟨loc, μ⟩).toNat (e.val ⟨loc, μ⟩)⟩)
    (hs : a.Safe lim ⟨loc, μ⟩ ∧ e.Safe lim ⟨loc, μ⟩ ∧ lim.Addr (a.val ⟨loc, μ⟩) := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    (hT : a.cost + e.cost + 1 ≤ T := by (first
                                         | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                             first
                                             | omega
                                             | (ring_nf; omega))
                                         | omega
                                         |
                                           (simp [] <;>
                                               first
                                               | omega
                                               | (ring_nf; omega)))) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.store a e) ⟨loc, μ⟩ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.store hs.1 hs.2.1 hs.2.2 hT h



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





/-- **Counting loops whose body changes no local variable.**  Before round j the local variables are
the given ones with j in the counter, and I j holds of the memory.  The bound hi has the value n
throughout, n fits in a word, and the body takes at most b steps. -/
theorem Ends.forMem {loc : ℕ → ℤ} {μ : ℕ → ℤ} {i : ℕ} {hi : _root_.ThreeSum1960614.Machine.Light.Expr} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} {T : ℕ}
    {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (I : ℕ → (ℕ → ℤ) → Prop) (n b : ℕ) (start : I 0 μ)
    (round : ∀ (j : ℕ) (μ' : ℕ → ℤ), j < n → I j μ' →
      _root_.ThreeSum1960614.Machine.Light.Ends lim P d body ⟨Function.update loc i j, μ'⟩ b fun σ' =>
        σ'.loc = Function.update loc i j ∧ I (j + 1) σ'.mem)
    (done : ∀ μ' : ℕ → ℤ, I n μ' → Q ⟨Function.update loc i n, μ'⟩)
    (bound : ∀ (j : ℕ) (μ' : ℕ → ℤ), j ≤ n → I j μ' →
      hi.Safe lim ⟨Function.update loc i j, μ'⟩ ∧ hi.val ⟨Function.update loc i j, μ'⟩ = n)
    (hn : (n : ℤ) ≤ lim.word := by omega)
    (hT : n * (hi.cost + b + 7) + hi.cost + 5 ≤ T := by (first
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
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.for i hi body) ⟨loc, μ⟩ T Q := by
  refine _root_.ThreeSum1960614.Machine.Light.Ends.for (fun j σ => σ.loc = Function.update loc i j ∧ I j σ.mem) n b
    ⟨by simp, start⟩ ?_ ?_ ?_ hn hT
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    refine (round j μ' hj hI).mono le_rfl ?_
    rintro ⟨_, μ''⟩ ⟨rfl, hI'⟩
    exact ⟨by simp, by simp, hI'⟩
  · rintro ⟨_, μ'⟩ - ⟨rfl, hI⟩
    exact done μ' hI
  · rintro j ⟨_, μ'⟩ hj - ⟨rfl, hI⟩
    exact bound j μ' hj hI

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
# A pass over an array

`pass c len dst e` is the loop "for c < len: dst[c] := e".  The rule `Ends.pass` says what it does:
if round j computes f j, then the loop writes f 0, …, f (n - 1) to the n cells from dst, changes
nothing else, and takes n (cost of e + 12) + 6 steps.  A routine whose only loop writes cell dst + c
in round c, with the length and dst in local variables, is an instance: its proof only says what
round j reads.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}



variable {μ : ℕ → ℤ} {dst j : ℕ} {f : ℕ → ℤ}

/-- After the pass the n cells hold the list of the values f 0, …, f (n - 1). -/
theorem seg_wrote {n : ℕ} {l : List ℤ} (hl : l.length = n)
    (h : ∀ i (hi : i < l.length), l[i] = f i) : _root_.ThreeSum1960614.Machine.Light.Seg (_root_.Light.wrote μ dst f n) dst l := fun i hi => by
  rw [_root_.ThreeSum1960614.Machine.Light.wrote_done (hl ▸ hi), h i hi]





end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# Copying and filling a segment

copy(src, dst, n) copies n cells from src to dst (the two segments do not overlap), within
`copyTime n` steps.  fill(dst, n, x) writes x into n cells from dst, within `fillTime n` steps.
Both change no other cell (`copy_meets`, `fill_meets`).  Each of the two is one pass over the cells
from dst, so `Ends.pass` says what it does, and the proof only says what round i reads.
-/

@[expose] public section

namespace Light
open _root_.Light


variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

/-! ## copy -/

namespace Copy
open _root_.Light.Copy







end Copy







/-! ## fill -/

namespace Fill
open _root_.Light.Fill







end Fill





/-- **fill(dst, n, x)** writes x into the n cells from dst and changes nothing else. -/
theorem fill_meets {p : ℕ} (hp : P[p]? = some _root_.ThreeSum1960614.Machine.Light.fillBody) {μ : ℕ → ℤ} {dst n : ℕ} {x : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hdst : dst + n ≤ lim.space) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [(dst : ℤ), n, x] μ (_root_.Light.fillTime n) fun _ μ' =>
      _root_.ThreeSum1960614.Machine.Light.Seg μ' dst (List.replicate n x) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst n :=
  _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp (_root_.ThreeSum1960614.Machine.Light.Ends.pass (fun _ => x) (fun i hi => by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)))
    ⟨_root_.ThreeSum1960614.Machine.Light.seg_wrote List.length_replicate fun i hi => List.getElem_replicate .., by (( try refine _root_.ThreeSum1960614.Machine.Light.SameOn.cell ?_
                                                                                                                       intro p2m_macro_10275487210966976721 p2m_macro_14496787206018393212
                                                                                                                       first
                                                                                                                       | ((  repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_13127251152367327910); (try have := p2m_macro_13127251152367327910 p2m_macro_10275487210966976721 (by omega)); revert p2m_macro_13127251152367327910)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                                                                                                                       |
                                                                                                                         (simp [] at p2m_macro_14496787206018393212;
                                                                                                                           ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_16154321206980007621); (try have := p2m_macro_16154321206980007621 p2m_macro_10275487210966976721 (by omega)); revert p2m_macro_16154321206980007621)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *); omega)
                                                                                                                       | ( ( repeat ((with_reducible rename _root_.ThreeSum1960614.Machine.Light.SameOn _ _ _ => p2m_macro_12998029695480404067); (try have := p2m_macro_12998029695480404067 p2m_macro_10275487210966976721 (by omega)); revert p2m_macro_12998029695480404067)
                                                                                                                             intros
                                                                                                                             try simp only [_root_.Function.update_apply, _root_.Light.wrote] at *)
                                                                                                                           fail "The cell x may have changed. Each equation ν' x = ν x above comes from a promise \
                                                                                                                                       SameOn K ν ν' whose condition holds at x. Look for the promise without an equation: \
                                                                                                                                       its condition K x does not follow from the hypotheses.")))⟩
    hw hdst rfl rfl (hT := by (first
                               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.Light.fillTime]
                                   first
                                   | omega
                                   | (ring_nf; omega))
                               | omega
                               |
                                 (simp [_root_.Light.fillTime] <;>
                                     first
                                     | omega
                                     | (ring_nf; omega)))))

end Light

end

end ThreeSum1960614.Machine

namespace ThreeSum1960614.Machine

/-!
# A Boolean support table with repeated keys

The routine clears the destination, then marks a key only when its validity
flag is one. Repeated retained representations set the same bit; this is
the support operation needed for a local hash-cover row.
-/

namespace ThreeSum.LightSupportMark
open _root_.ThreeSum.LightSupportMark


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset







theorem bit_zero (key valid : ℕ → ℕ) (r : ℕ) : _root_.ThreeSum.LightSupportMark.bit key valid r 0 = 0 := by
  simp [_root_.ThreeSum.LightSupportMark.bit,_root_.ThreeSum.LightSupportMark.Hit]

theorem hit_succ (key valid : ℕ → ℕ) (r i : ℕ) :
    _root_.ThreeSum.LightSupportMark.Hit key valid r (i+1) ↔ _root_.ThreeSum.LightSupportMark.Hit key valid r i ∨ (valid i=1 ∧ key i=r) := by
  simp only [_root_.ThreeSum.LightSupportMark.Hit,mem_range]
  constructor
  · rintro ⟨j,hj,hv,hk⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · exact Or.inl ⟨j,hj,hv,hk⟩
    · exact Or.inr ⟨hv,hk⟩
  · rintro (⟨j,hj,hv,hk⟩ | ⟨hv,hk⟩)
    · exact ⟨j,by omega,hv,hk⟩
    · exact ⟨i,by omega,hv,hk⟩

theorem bit_succ_of_hit (key valid : ℕ → ℕ) (r i : ℕ)
    (hv : valid i=1) (hk : key i=r) : _root_.ThreeSum.LightSupportMark.bit key valid r (i+1) = 1 :=
  if_pos ((_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.hit_succ key valid r i).mpr (Or.inr ⟨hv,hk⟩))

theorem bit_succ_of_not (key valid : ℕ → ℕ) (r i : ℕ)
    (h : ¬(valid i=1 ∧ key i=r)) : _root_.ThreeSum.LightSupportMark.bit key valid r (i+1) = _root_.ThreeSum.LightSupportMark.bit key valid r i := by
  unfold _root_.ThreeSum.LightSupportMark.bit
  by_cases hh : _root_.ThreeSum.LightSupportMark.Hit key valid r i
  · have hn : _root_.ThreeSum.LightSupportMark.Hit key valid r (i+1) := (_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.hit_succ key valid r i).mpr (Or.inl hh)
    simp only [if_pos hh,if_pos hn]
  · have hn : ¬_root_.ThreeSum.LightSupportMark.Hit key valid r (i+1) := by
      intro hi
      rcases (_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.hit_succ key valid r i).mp hi with hi | hi
      · exact hh hi
      · exact h hi
    simp only [if_neg hh,if_neg hn]





variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem mark_ends {μ : ℕ → ℤ} {loc : ℕ → ℤ} {keys flags dst n p : ℕ}
    (key valid : ℕ → ℕ)
    (hkeysLoc : loc 0=keys) (hflagsLoc : loc 1=flags) (hdstLoc : loc 2=dst) (hlen : loc 3=n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hK : keys+n ≤ lim.space) (hF : flags+n ≤ lim.space) (hD : dst+p ≤ lim.space)
    (hsepK : _root_.Light.Apart keys n dst p) (hsepF : _root_.Light.Apart flags n dst p)
    (hkeys : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags+i) = (valid i : ℤ))
    (hkeyLt : ∀ i < n, key i < p)
    (hzero : ∀ r < p, μ (dst+r)=0) (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.markBody ⟨loc,μ⟩ (_root_.ThreeSum.LightSupportMark.markTime n)
      (fun σ' => (∀ r < p, σ'.mem (dst+r) = (_root_.ThreeSum.LightSupportMark.bit key valid r n : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ σ'.mem dst p) := by
  let Inv := fun i (μ' : ℕ → ℤ) =>
    (∀ r < p, μ' (dst+r) = (_root_.ThreeSum.LightSupportMark.bit key valid r i : ℤ)) ∧ _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.markBody
  apply _root_.ThreeSum1960614.Machine.Light.Ends.forMem Inv n 32 (hn := by omega) (hT := by unfold _root_.ThreeSum.LightSupportMark.markTime; (first
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
  · exact ⟨by simpa only [_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.bit_zero,Nat.cast_zero] using hzero,_root_.ThreeSum1960614.Machine.Light.SameOutside.refl⟩
  · intro i μ' hi hI
    obtain ⟨hbits,hsame⟩ := hI
    have hk := hkeyLt i hi
    have hkr : μ' (keys+i) = (key i : ℤ) := (hsame _ (by omega)).trans (hkeys i hi)
    have hfr : μ' (flags+i) = (valid i : ℤ) := (hsame _ (by omega)).trans (hflags i hi)
    refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun hc => ?_) (fun hc => ?_)
      (by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hflagsLoc, hfr] <;> omega)))
    · have hv : valid i=1 := by simpa [hflagsLoc,hfr] using hc
      have ha : (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5))))).val ⟨Function.update loc 5 (i : ℤ),μ'⟩ =
          ((dst+key i : ℕ) : ℤ) := by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkeysLoc, hdstLoc, hkr] <;> omega))
      refine _root_.ThreeSum1960614.Machine.Light.Ends.storeLast ?_ (by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, hkeysLoc, hdstLoc, hkr] <;> omega))) (by (first
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
      change Function.update loc 5 (i : ℤ) = Function.update loc 5 (i : ℤ) ∧
        Inv (i+1) (Function.update μ' ((((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 2) (_root_.ThreeSum1960614.Machine.Light.M ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) (_root_.ThreeSum1960614.Machine.Light.v 0) (_root_.ThreeSum1960614.Machine.Light.v 5))))).val
          ⟨Function.update loc 5 (i : ℤ),μ'⟩).toNat 1)
      rw [ha,Int.toNat_natCast]
      refine ⟨rfl,?_,hsame.update ⟨by omega,by omega⟩ 1⟩
      intro r hr
      by_cases he : key i=r
      · subst r
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.bit_succ_of_hit key valid (key i) i hv rfl]
        simp
      · rw [Function.update_of_ne (by omega),hbits r hr]
        rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.bit_succ_of_not key valid r i (by tauto)]
    · have hv : valid i≠1 := by simpa [hflagsLoc,hfr] using hc
      apply _root_.ThreeSum1960614.Machine.Light.Ends.skip
      refine ⟨rfl,?_,hsame⟩
      intro r hr
      rw [_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.bit_succ_of_not key valid r i (by tauto)]
      exact hbits r hr
  · intro μ' hI
    exact hI
  · intro i μ' hi hI
    simp [hlen]









end ThreeSum.LightSupportMark

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightSupportMark
open _root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.Finset
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightSupportMark.meets__implementation_7043fa12cc {pMain pFill : ℕ}
    (hmain : P[pMain]? = some (_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.body pFill)) (hfill : P[pFill]? = some _root_.ThreeSum1960614.Machine.Light.fillBody)
    {μ : ℕ → ℤ} {keys flags dst n p : ℕ}
    (key valid : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hK : keys+n ≤ lim.space) (hF : flags+n ≤ lim.space) (hD : dst+p ≤ lim.space)
    (hsepK : _root_.Light.Apart keys n dst p) (hsepF : _root_.Light.Apart flags n dst p)
    (hkeys : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hflags : ∀ i < n, μ (flags+i) = (valid i : ℤ))
    (hkeyLt : ∀ i < n, key i < p) (hword : (1 : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P pMain d [keys,flags,dst,n,p] μ (_root_.ThreeSum.LightSupportMark.time n p)
      (fun _ μ' => (∀ r < p, μ' (dst+r) = (_root_.ThreeSum.LightSupportMark.bit key valid r n : ℤ)) ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ μ' dst p) := by
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hmain
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.body _root_.ThreeSum.LightSupportMark.time
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
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen ((_root_.ThreeSum1960614.Machine.Light.fill_meets (d := d + 1) (μ := μ) (dst := dst) (n := p) (x := 0) hfill hw hD) _ (by omega)) ?_ ?_ ?_ ?_
     | refine _root_.ThreeSum1960614.Machine.Light.Ends.callToThen (_root_.ThreeSum1960614.Machine.Light.fill_meets (d := d + 1) (μ := μ) (dst := dst) (n := p) (x := 0) hfill hw hD) ?_ ?_ ?_ ?_
     on_goal -1 =>
       first
       | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightSupportMark.markTime]
           first
           | omega
           | (ring_nf; omega))
       | omega
       |
         (simp [_root_.ThreeSum.LightSupportMark.markTime] <;>
             first
             | omega
             | (ring_nf; omega))
     on_goal -1 => omega
     on_goal -1 =>
       ( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption))
         (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption))
         simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, _root_.ThreeSum.LightSupportMark.markTime] <;> omega)
     on_goal -1 => (rintro v μ₁ ⟨hfilled, hkept⟩; try with_unfolding_none refine _root_.ThreeSum1960614.Machine.Light.Ends.skip ?_))
  have hkr : ∀ i < n, μ₁ (keys+i) = (key i : ℤ) := by
    intro i hi
    exact (hkept _ (by omega)).trans (hkeys i hi)
  have hfr : ∀ i < n, μ₁ (flags+i) = (valid i : ℤ) := by
    intro i hi
    exact (hkept _ (by omega)).trans (hflags i hi)
  have hzero : ∀ r < p, μ₁ (dst+r)=0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply _root_.ThreeSum1960614.Machine.Light.Ends.pieceLast (_root_.ThreeSum1960614.Machine.ThreeSum.LightSupportMark.mark_ends key valid (by simp) (by simp) (by simp) (by simp)
    hw hK hF hD hsepK hsepF hkr hfr hkeyLt hzero hword)
  · intro σ' hpost
    exact ⟨hpost.1,fun a ha => (hpost.2 a ha).trans (hkept a ha)⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightSupportMark.meets__implementation_7043fa12cc) := (@ThreeSum1960614.Machine.ThreeSum.LightSupportMark.meets__implementation_7043fa12cc)

#print axioms solution
