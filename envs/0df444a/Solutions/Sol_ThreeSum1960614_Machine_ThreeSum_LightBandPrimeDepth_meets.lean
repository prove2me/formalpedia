-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T07:17:46.357996+00:00
-- url     : https://prove2.me/submissions/6e188a93-fbc0-4465-8e3c-72ed5d0c72b5

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
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
import Definitions.Def_ThreeSum1962Source_Bundle01
import Definitions.Def_ThreeSum1962Source_Bundle02
import Definitions.Def_ThreeSum1962Source_Bundle04
import Definitions.Def_ThreeSum1962Source_Bundle05
import Definitions.Def_ThreeSum1962Source_Bundle07
import Lean
import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
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
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Sqrt
import Mathlib.Data.Real.Basic
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
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
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_of_blockSafe
import Theorems.Thm_ThreeSum1960614_Machine_Light_Ends_while

namespace Light
end Light
namespace ThreeSum
end ThreeSum
namespace ThreeSum.LightBandPrimeDepth
end ThreeSum.LightBandPrimeDepth
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum
end ThreeSum1960614.Machine.ThreeSum
namespace ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth
end ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth

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























/-- Loops in which every round costs at most b. -/
theorem Ends.whileConst {σ c s T} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (I : ℕ → _root_.ThreeSum1960614.Machine.Light.State → Prop) (n b : ℕ) (hI : I 0 σ)
    (hs : ∀ i σ, i < n → I i σ → c.Safe lim σ ∧ c.Holds σ ∧ _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ b (I (i + 1)))
    (hn : ∀ σ, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + b) + (c.cost + 1) ≤ T) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c s) σ T Q :=
  (_root_.ThreeSum1960614.Machine.Light.Ends.while I n (fun _ => b) hI hs hn).mono (by simpa using hT) fun _ h => h





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











/-- **Blocks.**  A block that runs safely from σ ends within any T ≥ s.blockCost, in the state
s.after σ. -/
theorem Ends.block {s : _root_.ThreeSum1960614.Machine.Light.Stmt} {σ : _root_.ThreeSum1960614.Machine.Light.State} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop} (h : s.Runs lim σ Q)
    (hT : s.blockCost ≤ T := by (first
                                 | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, ]
                                     first
                                     | omega
                                     | (ring_nf; omega))
                                 | omega
                                 |
                                   (simp [] <;>
                                       first
                                       | omega
                                       | (ring_nf; omega)))) : _root_.ThreeSum1960614.Machine.Light.Ends lim P d s σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.of_blockSafe h.1 hT h.2

/-! ## Sequencing: what is left of the time goes to the rest of the program -/





























/-! ## Loops whose body is a block -/

/-- **Loops whose body is a block.**  I j is the invariant before round j of n rounds.  The time is
computed from body.blockCost. -/
theorem Ends.whileBlock {σ : _root_.ThreeSum1960614.Machine.Light.State} {c : _root_.ThreeSum1960614.Machine.Light.Cond} {body : _root_.ThreeSum1960614.Machine.Light.Stmt} {T : ℕ} {Q : _root_.ThreeSum1960614.Machine.Light.State → Prop}
    (I : ℕ → _root_.ThreeSum1960614.Machine.Light.State → Prop) (n : ℕ) (start : I 0 σ)
    (round : ∀ (j : ℕ) (σ : _root_.ThreeSum1960614.Machine.Light.State), j < n → I j σ →
      c.Safe lim σ ∧ c.Holds σ ∧ body.Runs lim σ (I (j + 1)))
    (done : ∀ σ : _root_.ThreeSum1960614.Machine.Light.State, I n σ → c.Safe lim σ ∧ ¬ c.Holds σ ∧ Q σ)
    (hT : n * (c.cost + 1 + body.blockCost) + (c.cost + 1) ≤ T := by (first
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
    _root_.ThreeSum1960614.Machine.Light.Ends lim P d (_root_.ThreeSum1960614.Machine.Light.Stmt.while c body) σ T Q :=
  _root_.ThreeSum1960614.Machine.Light.Ends.whileConst I n body.blockCost start
    (fun j σ hj hI => ⟨(round j σ hj hI).1, (round j σ hj hI).2.1,
      _root_.ThreeSum1960614.Machine.Light.Ends.block (round j σ hj hI).2.2 le_rfl⟩) done hT

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

section
open _root_.ThreeSum
open _root_.ThreeSum1960614.Machine.ThreeSum

open _root_.ThreeSum.LightBandPrimeDepth
open _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 1200000
set_option maxRecDepth 8000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.meets__implementation_f814b10bd4 {p : ℕ} (hp : P[p]?=some _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.body) (hy : 0 < y)
    (hword : (_root_.ThreeSum.LightBandPrimeDepth.word R y : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [R,y] μ (_root_.ThreeSum.LightBandPrimeDepth.time R y)
      (fun result ν => result=(_root_.ThreeSum.LightBandPrimeDepth.depth R y : ℤ) ∧ ν=μ) := by
  have hbase : 1 < 4*y := by omega
  have hltq := Nat.lt_pow_succ_log_self hbase (R/4)
  simp only [Nat.succ_eq_add_one] at hltq
  have hlt : R < 4*(4*y)^(_root_.ThreeSum.LightBandPrimeDepth.depth R y+1) := by unfold _root_.ThreeSum.LightBandPrimeDepth.depth; omega
  have hdepth : _root_.ThreeSum.LightBandPrimeDepth.depth R y ≤ R := (Nat.log_le_self _ _).trans (Nat.div_le_self _ _)
  have hstart : (16*y : ℕ) ≤ _root_.ThreeSum.LightBandPrimeDepth.word R y := by unfold _root_.ThreeSum.LightBandPrimeDepth.word; nlinarith
  have hR : (R : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandPrimeDepth.word; omega : R ≤ word R y)).trans hword
  have hR1Word : (R : ℤ)+1 ≤ lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr (by unfold _root_.ThreeSum.LightBandPrimeDepth.word; omega : R+1 ≤ word R y)).trans hword
  have hstartWord : ((16*y : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hstart).trans hword
  have hdepthWord : (_root_.ThreeSum.LightBandPrimeDepth.depth R y : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hdepth).trans hR
  have hpower (i : ℕ) (hi : i ≤ _root_.ThreeSum.LightBandPrimeDepth.depth R y) : 4*(4*y)^(i+1) ≤ _root_.ThreeSum.LightBandPrimeDepth.word R y := by
    by_cases hz : R/4=0
    · have hi0 : i=0 := by simp only [_root_.ThreeSum.LightBandPrimeDepth.depth,hz,Nat.log_zero_right] at hi; omega
      subst i
      simpa only [Nat.zero_add,pow_one,← Nat.mul_assoc,show 4*4=16 by decide] using hstart
    · have hiLog : i ≤ Nat.log (4*y) (R/4) := hi
      have hp := (Nat.pow_le_pow_right hbase.le hiLog).trans (Nat.pow_log_le_self _ hz)
      have h4 : 4*(4*y)^i ≤ R := by omega
      have hm := Nat.mul_le_mul_right (4*y) h4
      rw [pow_succ]
      unfold _root_.ThreeSum.LightBandPrimeDepth.word
      nlinarith
  have hinit : 4*(4*y)^(0+1)=16*y := by ring
  have hfourWord : (4 : ℤ)*(y : ℤ) ≤ lim.word := by
    have hh : 4*y ≤ _root_.ThreeSum.LightBandPrimeDepth.word R y := by omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.body _root_.ThreeSum.LightBandPrimeDepth.time
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
  (focus
     ((first
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
         | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
       repeat
         with_unfolding_none
           first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
     refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (16 * y : ℕ) ?_ ?_ ?_
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
  refine _root_.ThreeSum1960614.Machine.Light.Ends.next _ (_root_.ThreeSum1960614.Machine.Light.Ends.whileBlock (T := 30*_root_.ThreeSum.LightBandPrimeDepth.depth R y+10) (fun i σ =>
    σ=⟨_root_.Light.frame [R,y,i,(4*(4*y)^(i+1) : ℕ)],μ⟩)
    (_root_.ThreeSum.LightBandPrimeDepth.depth R y) (by simp; rw [show (16 : ℤ)*(y : ℤ)=4*(4*(y : ℤ)) by ring]) ?round ?done (by simp; omega))
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
  case round =>
    rintro i _ hi rfl
    have hqne : R/4 ≠ 0 := by
      intro hz
      simp [_root_.ThreeSum.LightBandPrimeDepth.depth,hz] at hi
    have hiLog : i+1 ≤ Nat.log (4*y) (R/4) := by change i < Nat.log (4*y) (R/4) at hi; omega
    have hpow : (4*y)^(i+1) ≤ R/4 :=
      (Nat.pow_le_pow_right hbase.le hiLog).trans (Nat.pow_log_le_self _ hqne)
    have hle : 4*(4*y)^(i+1) ≤ R := by omega
    have hic : i+1 ≤ R := by omega
    have hcurrentWord : ((4*(4*y)^(i+1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hpower i (by omega))).trans hword
    have hnext : 4*y*(4*(4*y)^(i+1)) ≤ _root_.ThreeSum.LightBandPrimeDepth.word R y := by
      have hh := Nat.mul_le_mul_left (4*y) hle
      unfold _root_.ThreeSum.LightBandPrimeDepth.word
      nlinarith
    have hnextZ : ((4*y*(4*(4*y)^(i+1)) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hnext).trans hword
    have heq : 4*(4*y)^(i+1+1)=4*y*(4*(4*y)^(i+1)) := by ring
    rw [heq]
    generalize 4*(4*y)^(i+1)=q at hle hnextZ hcurrentWord ⊢
    have hprodZ : (4 : ℤ)*(y : ℤ)*(q : ℤ) ≤ lim.word := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hnextZ
    have hprodN : (0 : ℤ) ≤ (4 : ℤ)*(y : ℤ)*(q : ℤ) := by positivity
    exact ⟨by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),by simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hlastWord : ((4*(4*y)^(_root_.ThreeSum.LightBandPrimeDepth.depth R y+1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hpower _ le_rfl)).trans hword
    generalize 4*(4*y)^(_root_.ThreeSum.LightBandPrimeDepth.depth R y+1)=q at hlt hlastWord ⊢
    refine ⟨by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),?_⟩
    (focus
       ((first
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
           | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
         repeat
           with_unfolding_none
             first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
       refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum.LightBandPrimeDepth.depth R y) ?_ ?_ ?_
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
    exact ⟨rfl,rfl⟩
end

end

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.meets__implementation_f814b10bd4) := (@ThreeSum1960614.Machine.ThreeSum.LightBandPrimeDepth.meets__implementation_f814b10bd4)

#print axioms solution
