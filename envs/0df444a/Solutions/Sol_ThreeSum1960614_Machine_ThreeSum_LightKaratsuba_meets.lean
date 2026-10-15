-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:07:08.814188+00:00
-- url     : https://prove2.me/submissions/61361066-010a-4e10-9d5d-61bd37a7c6c1

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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Lean
import Lean.Elab.Tactic.Omega
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
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Data.Int.Notation
import Mathlib.Data.List.GetD
import Mathlib.Data.Nat.Count
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Notation
import Mathlib.Data.Nat.SuccPred
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Logic.Function.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightKaratsuba_recurse_ends

namespace Light
end Light
namespace Polynomial
end Polynomial
namespace ThreeSum
end ThreeSum
namespace ThreeSum.Karatsuba
end ThreeSum.Karatsuba
namespace ThreeSum.LightKaratsuba
end ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.Karatsuba
end ThreeSum1960614.Machine.ThreeSum.Karatsuba
namespace ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
end ThreeSum1960614.Machine.ThreeSum.LightKaratsuba
namespace ThreeSum1960614.Machine.ThreeSumApsp
end ThreeSum1960614.Machine.ThreeSumApsp
namespace ThreeSumApsp
end ThreeSumApsp

namespace ThreeSum1960614.Machine

/-!
# Dense integer Karatsuba multiplication

This file implements a dense, low-coefficient-first list algorithm. Its
correctness theorem is an equality of integer polynomials. The instrumented
work model counts list traversal and scalar arithmetic primitives; it is a
separate obligation to compile this implementation to `Light` and prove the
benchmark's word-RAM step and word-size bounds.
-/

namespace ThreeSum.Karatsuba
open _root_.ThreeSum.Karatsuba


open _root_.Polynomial



























theorem asPolynomial_head {as : List ℤ} (h : as.length ≤ 1) :
    _root_.ThreeSum.Karatsuba.asPolynomial as = C (as.headD 0) := by
  cases as with
  | nil => simp [_root_.ThreeSum.Karatsuba.asPolynomial]
  | cons a as =>
    have hz : as.length = 0 := by simpa using h
    have he : as = [] := List.length_eq_zero_iff.mp hz
    subst as
    simp [_root_.ThreeSum.Karatsuba.asPolynomial]









/-! ## Explicit traversal/arithmetic work model

The following charges reflect the operations in the executable list code:
two units per matched coefficient of `plus`; two per mapped coefficient of
`negate`; two per generated/concatenated zero of `shift`; and the two scans
used by `take` and `drop`. The fixed per-call charges include list tests.
They are a conventional unit-cost list/arithmetic model, **not** a theorem
about the benchmark machine or Lean's runtime system.

The recursive charge below uses the actual intermediate list sizes. The
uniform three-subcall recurrence is proved from those sizes; it is not an
assumption that the desired multiplication bound already holds.
-/





















end ThreeSum.Karatsuba

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













/-- Reading a cell of a segment, with a default value for the list. -/
theorem Seg.getD (h : _root_.ThreeSum1960614.Machine.Light.Seg μ a l) {i : ℕ} (hi : i < l.length) (d : ℤ) : μ (a + i) = l.getD i d := by
  rw [h i hi, List.getD_eq_getElem _ _ hi]

































































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
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba
open _root_.ThreeSum.LightKaratsuba


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial











































section Join

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d pLinear pFill : ℕ}



end Join

section BaseCase

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ}

theorem base_ends {μ : ℕ → ℤ} {a b out work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + 1 ≤ lim.space) (hb : b + 1 ≤ lim.space)
    (hout : out + 2 ≤ lim.space) (hmul : |μ a * μ b| ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.baseBody ⟨_root_.Light.frame [1, a, b, out, work], μ⟩ 12 fun σ' =>
      σ'.mem out = μ a * μ b ∧ σ'.mem (out + 1) = 0 ∧
        _root_.ThreeSum1960614.Machine.Light.SameOutside μ σ'.mem out 2 := by
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.baseBody
  have hm := abs_le.mp hmul
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen out (μ a * μ b) ?_ ?_ ?_
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
     refine _root_.ThreeSum1960614.Machine.Light.Ends.storeToThen (out + 1) 0 ?_ ?_ ?_
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
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · intro j hj
    simp only [Function.update_of_ne (by omega : j ≠ out + 1),
      Function.update_of_ne (by omega : j ≠ out)]

theorem base_product {μ μ' : ℕ → ℤ} {a b out : ℕ} {as bs : List ℤ}
    (ha : _root_.ThreeSum1960614.Machine.Light.Seg μ a as) (hb : _root_.ThreeSum1960614.Machine.Light.Seg μ b bs)
    (hAlen : as.length = 1) (hBlen : bs.length = 1)
    (hzero : μ' out = μ a * μ b) (hone : μ' (out + 1) = 0) :
    _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ProductAt μ' out 1 as bs := by
  have hA := _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_head hAlen.le
  have hB := _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.asPolynomial_head hBlen.le
  have hhead (xs : List ℤ) : xs.getD 0 0 = xs.headD 0 := by cases xs <;> rfl
  have hreadA : μ a = as.headD 0 := by
    simpa only [Nat.add_zero, hhead] using ha.getD (by omega : 0 < as.length) 0
  have hreadB : μ b = bs.headD 0 := by
    simpa only [Nat.add_zero, hhead] using hb.getD (by omega : 0 < bs.length) 0
  intro j hj
  rw [hA, hB, ← map_mul]
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simpa only [Nat.add_zero, Polynomial.coeff_C_zero, hreadA, hreadB] using hzero
  · simpa only [Polynomial.coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0)] using hone

end BaseCase













theorem ten_temp_le_word (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ _root_.ThreeSum.LightKaratsuba.wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold _root_.ThreeSum.LightKaratsuba.wordBound
  nlinarith







section RecursiveExecution

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}



end RecursiveExecution

section CompleteProcedure

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}









end CompleteProcedure

end ThreeSum.LightKaratsuba

end ThreeSum1960614.Machine

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
open _root_.ThreeSum.Karatsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba
open _root_.Polynomial
open _root_.ThreeSum.LightKaratsuba
open _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba

variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {pSelf pHalf pLinear pFill : ℕ}
section

/-- Correctness, preservation, word safety, call depth, and actual Light
step count for the fixed recursive multiplication procedure. -/
theorem ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets__implementation_d696f2a910 (C : _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Procs P pSelf pHalf pLinear pFill)
    (hw : (lim.space : ℤ) ≤ lim.word)
    {k a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k)
    (hAseg : _root_.ThreeSum1960614.Machine.Light.Seg μ a as) (hBseg : _root_.ThreeSum1960614.Machine.Light.Seg μ b bs)
    (hA : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound as (U : ℤ)) (hB : _root_.ThreeSum1960614.Machine.ThreeSum.Karatsuba.CoeffBound bs (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (_root_.ThreeSum.LightKaratsuba.wordBound (2 ^ k) U : ℤ) ≤ lim.word) :
    ∀ d, d + k + 1 ≤ lim.depth →
      _root_.ThreeSum1960614.Machine.Light.Meets lim P pSelf d [2 ^ k, a, b, out, work] μ (_root_.ThreeSum.LightKaratsuba.time k)
        (fun _ μ' => _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.Result μ out (2 ^ k) work as bs μ') := by
  induction k generalizing a b out work U as bs μ with
  | zero =>
    simp only [pow_zero] at hAlen hBlen haf hbf hof hspace hword ⊢
    intro d hd
    have hvA : |μ a| ≤ (U : ℤ) := by
      have hr := hAseg.getD (by omega : 0 < as.length) 0
      simpa only [← hr, Nat.add_zero] using hA 0
    have hvB : |μ b| ≤ (U : ℤ) := by
      have hr := hBseg.getD (by omega : 0 < bs.length) 0
      simpa only [← hr, Nat.add_zero] using hB 0
    have hp : |μ a * μ b| ≤ (U : ℤ) ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hvA hvB (abs_nonneg _) (Nat.cast_nonneg U)
    have hpw : (U : ℤ) ^ 2 ≤ lim.word := by
      have hh : 10 * ((4 * 1 * U ^ 2 : ℕ) : ℤ) ≤ _root_.ThreeSum.LightKaratsuba.wordBound 1 U := by
        exact_mod_cast _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.ten_temp_le_word 1 U (by decide)
      push_cast at hh
      nlinarith only [hh, hword, sq_nonneg (U : ℤ)]
    have hbases := _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.base_ends (P := P) (d := d) (a := a) (b := b) (out := out) (work := work)
      hw (by omega) (by omega) (by omega) (hp.trans hpw)
    refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.self ?_
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.body
    refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun hc => False.elim (by simpa using hc)) (fun _ => ?_)
      (hT := by simp [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost])
    refine hbases.mono (by norm_num [_root_.ThreeSum.LightKaratsuba.time, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost]) ?_
    intro σ' hr
    exact ⟨_root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.base_product hAseg hBseg hAlen hBlen hr.1 hr.2.1,
      fun j hj => hr.2.2 j hj.2⟩
  | succ k ih =>
    intro d hd
    have hp : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
    have hpZ : (0 : ℤ) < (2 : ℤ) ^ k := pow_pos (by norm_num) k
    have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    have heZ : (2 : ℤ) ^ (k + 1) = 2 * ((2 ^ k : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ, mul_comm]
    rw [he] at hAlen hBlen haf hbf hof hspace hword ⊢
    rw [heZ]
    refine _root_.ThreeSum1960614.Machine.Light.Meets.of_body C.self ?_
    unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.body
    refine _root_.ThreeSum1960614.Machine.Light.Ends.iteLast (fun _ => ?_) (fun hc => ?_)
      (hT := by (first
                 | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum.LightKaratsuba.time]
                     first
                     | omega
                     | (ring_nf; omega))
                 | omega
                 |
                   (simp [_root_.ThreeSum.LightKaratsuba.time] <;>
                       first
                       | omega
                       | (ring_nf; omega))))
    · exact _root_.ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.recurse_ends C rfl hw hAlen hBlen hAseg hBseg hA hB
        haf hbf hof hspace hword (by omega)
        (fun a' b' out' work' U' as' bs' μ' hla hlb hsa hsb hba hbb
          hfa hfb hfo hsp hwo =>
          ih hla hlb hsa hsb hba hbb hfa hfb hfo hsp hwo (d + 1) (by omega))
    · have hfalse : ¬ (1 : ℤ) < 2 * (2 : ℤ) ^ k := by simpa using hc
      have hone : (1 : ℤ) ≤ (2 : ℤ) ^ k := hpZ
      omega
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets__implementation_d696f2a910) := (@ThreeSum1960614.Machine.ThreeSum.LightKaratsuba.meets__implementation_d696f2a910)

#print axioms solution
