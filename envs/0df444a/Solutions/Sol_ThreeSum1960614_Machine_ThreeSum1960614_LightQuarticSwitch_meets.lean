-- Prove2me | solution 1 for ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.meets
-- status  : ACCEPTED   (prove)
-- author  : @Yuxuan Xu
-- created : 2026-10-15T06:48:35.333326+00:00
-- url     : https://prove2.me/submissions/3357056f-b5ad-471f-b0b3-c70be270064b

/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/

import Definitions.Def_APSPSource_RemainingDefinitions
import Definitions.Def_APSPSource_ThreeSumApsp_Lang_Syntax
import Definitions.Def_ThreeSum1960614_Analysis
import Definitions.Def_ThreeSum1960614_Machine_Bundle003
import Definitions.Def_ThreeSum1960614_Machine_Bundle004
import Definitions.Def_ThreeSum1960614_Machine_Bundle006
import Definitions.Def_ThreeSum1960614_Machine_Bundle007
import Definitions.Def_ThreeSum1960614_Machine_Bundle008
import Definitions.Def_ThreeSum1960614_Machine_Bundle009
import Definitions.Def_ThreeSum1960614_Machine_Bundle010
import Definitions.Def_ThreeSum1960614_Machine_Bundle012
import Definitions.Def_ThreeSum1962Source_Bundle04
import Lean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Algebra.Order.Group.Unbundled.Abs
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Log
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic
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
import Theorems.Thm_ThreeSum1960614_Machine_ThreeSum_LightSwitchScalar_scalar_safe

namespace Light
end Light
namespace ThreeSum1960614
end ThreeSum1960614
namespace ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.LightQuarticSwitch
namespace ThreeSum1960614.Machine.Light
end ThreeSum1960614.Machine.Light
namespace ThreeSum1960614.Machine.ThreeSum1960614
end ThreeSum1960614.Machine.ThreeSum1960614
namespace ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch
end ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch

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

namespace ThreeSum1960614.Machine

/-!
The actual quartic integer test and its Light-language execution contract.
The finite scan and proof structure adapt the pinned Apache-2.0 source
Submission/ThreeSum/LightSwitch{,Bounds}.lean, commit
2b639655e07421b9ac743de9090459bab473a7c0.
The coefficients, powers and resource allowances below are changed to
the exact expansion-232 degree-four comparison in PROOF.md, Section 4.2.
-/

namespace ThreeSum1960614.LightQuarticSwitch
open _root_.ThreeSum1960614.LightQuarticSwitch


open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

















@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r ↔ q ≤ r/2 ∧ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts J j r q := by
  simp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates, Nat.lt_succ_iff]

theorem index_mem {J j r : ℕ} (h : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r ∈ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index, dif_pos h]
  exact Finset.min'_mem _ _

theorem index_le {J j r q : ℕ} (hq : q ∈ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r) : _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r ≤ q := by
  have h : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty := ⟨q,hq⟩
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index, dif_pos h]
  exact Finset.min'_le _ _ hq

theorem before_rejects {J j r q : ℕ}
    (hne : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) (hq : q < _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor J j*_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial r q < _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left J j r := by
  have hb := (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_mem hne)).1
  have hno : ¬ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts J j r q := by
    intro h
    have hm := _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_le (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.mem_candidates.mpr ⟨by omega,h⟩)
    omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.accepts at hno
  omega

theorem at_accepts {J j r : ℕ} (hne : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left J j r ≤ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor J j*_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial r (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r) :=
  (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_mem hne)).2

theorem index_le_residual {J j r : ℕ} (hne : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r ≤ r :=
  (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.mem_candidates.mp (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_mem hne)).1.trans (Nat.div_le_self _ _)









variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J j r q d : ℕ}

theorem frame_vars_bound (hj : j ≤ J) (hq : q ≤ r) :
    ∀ i, |(_root_.Light.frame [(J : ℤ),j,r,q]) i| ≤ ((J+r+1000000001 : ℕ) : ℤ) := by
  intro i
  rcases i with _ | _ | _ | _ | i <;> simp [_root_.Light.frame] <;> omega

theorem test_safe (hj : j ≤ J) (hq : q ≤ r)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.word J r : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test.Safe lim ⟨_root_.Light.frame [(J : ℤ),j,r,q],μ⟩ := by
  have hv := _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.frame_vars_bound hj hq
  have hB : 2 ≤ J+r+1000000001 := by omega
  unfold _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test _root_.ThreeSum1960614.Machine.Light.Cond.Safe
  constructor
  · apply _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe hB _ hv
      _ (by
        simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.Small, and_true, true_and, and_assoc]
        exact ⟨by omega, by omega, by omega, by omega, by omega⟩)
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 500000000) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.sub) (Light.v 0) (Light.v 1))) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 785174904) (Light.v 2)) (Light.v 2)) (Light.v 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 72447023) (Light.v 2)) (Light.v 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (Light.v 3) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 24044466) (Light.v 2)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 12022459) (Light.v 3)))))))))).cost ≤ 96))).trans hword
  · apply _root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.scalar_safe hB _ hv
      _ (by
        simp only [_root_.ThreeSum1960614.Machine.ThreeSum.LightSwitchScalar.Small, and_true, true_and, and_assoc]
        exact ⟨by omega, by omega, by omega⟩)
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : (((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 100000000) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.add) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 159243801) (Light.v 0)) ((_root_.ThreeSum1960614.Machine.Light.Expr.op _root_.Light.Op.mul) (k 500000000) (Light.v 1)))) (Light.v 2)) (Light.v 2)) (Light.v 2)) (Light.v 2))).cost ≤ 96))).trans hword

theorem test_holds_iff (hj : j ≤ J) :
    _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test.Holds ⟨_root_.Light.frame [(J : ℤ),j,r,q],μ⟩ ↔ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor J j*_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial r q < _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left J j r := by
  simp only [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test,_root_.ThreeSum1960614.Machine.Light.Cond.Holds,_root_.ThreeSum1960614.Machine.Light.Expr.val,_root_.Light.Op.eval,_root_.Light.frame,List.getD_cons_zero,
    List.getD_cons_succ,Nat.cast_add,Nat.cast_ofNat]
  unfold _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.factor _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.polynomial _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.left
  exact_mod_cast (Iff.rfl :
    500000000*(J-j)*(q*(785174904*r*r*r+q*(72447023*r*r+q*(24044466*r+12022459*q)))) <
      100000000*(159243801*J+500000000*j)*r*r*r*r ↔
    500000000*(J-j)*(q*(785174904*r*r*r+q*(72447023*r*r+q*(24044466*r+12022459*q)))) <
      100000000*(159243801*J+500000000*j)*r*r*r*r)







end ThreeSum1960614.LightQuarticSwitch

end ThreeSum1960614.Machine

section
open _root_.ThreeSum1960614
open _root_.ThreeSum1960614.Machine.ThreeSum1960614

open _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch

open _root_.Light
open _root_.ThreeSum1960614.Machine.Light
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000
variable {lim : _root_.ThreeSum1960614.Machine.Light.Limits} {P : _root_.ThreeSum1960614.Machine.Light.Program} {μ : ℕ→ℤ} {J j r q d : ℕ}
section

theorem ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.meets__implementation_44279ce992 {p : ℕ} (hp : P[p]?=some _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.body) (hj : j ≤ J)
    (hne : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.candidates J j r).Nonempty)
    (hword : (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.word J r : ℤ) ≤ lim.word) :
    _root_.ThreeSum1960614.Machine.Light.Meets lim P p d [J,j,r] μ (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.time r)
      (fun result ν => result=(_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r : ℤ) ∧ ν=μ) := by
  have hindex := _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index_le_residual hne
  have hbase : J+r+1000000001 ≤ _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.word J r :=
    Nat.le_self_pow (by decide : (96 : ℕ) ≠ 0) _
  have hlinear : ((J+r+1000000001 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hbase).trans hword
  apply _root_.ThreeSum1960614.Machine.Light.Meets.of_body hp
  unfold _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.body _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.time
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
  refine _root_.ThreeSum1960614.Machine.Light.Ends.next (150*_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r+100) (_root_.ThreeSum1960614.Machine.Light.Ends.whileBlock
    (fun i σ => σ=⟨_root_.Light.frame [(J : ℤ),j,r,i],μ⟩)
    (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r) (by simp) ?round ?done (by (first
                                                                                                                | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test]
                                                                                                                    first
                                                                                                                    | omega
                                                                                                                    | (ring_nf; omega))
                                                                                                                | omega
                                                                                                                |
                                                                                                                  (simp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test] <;>
                                                                                                                      first
                                                                                                                      | omega
                                                                                                                      | (ring_nf; omega)))))
    (hT := by (first
               | ( simp only [_root_.ThreeSum1960614.Machine.Light.Stmt.blockCost, _root_.ThreeSum1960614.Machine.Light.Cond.cost, _root_.ThreeSum1960614.Machine.Light.Expr.cost, _root_.List.map_cons, _root_.List.map_nil, _root_.List.sum_cons, _root_.List.sum_nil, _root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test]
                   first
                   | omega
                   | (ring_nf; omega))
               | omega
               |
                 (simp [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test] <;>
                     first
                     | omega
                     | (ring_nf; omega))))
  case round =>
    rintro i _ hi rfl
    have hle : i ≤ r := by omega
    refine ⟨_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test_safe hj hle hword,
      (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test_holds_iff hj).mpr (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.before_rejects hne hi),by (( (try have := _root_.ThreeSum1960614.Machine.Light.Std.space_le (by assumption)); (try have := _root_.ThreeSum1960614.Machine.Light.Std.const_le (by assumption)); simp [_root_.ThreeSum1960614.Machine.Light.Limits.Addr, _root_.abs_le, -_root_.abs_mul, ] <;> omega)),?_⟩
    simp [_root_.ThreeSum1960614.Machine.Light.update_frame_setLocal]
  case done =>
    rintro _ rfl
    refine ⟨_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test_safe hj hindex hword,?_,?_⟩
    · rw [_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.test_holds_iff hj]
      exact not_lt_of_ge (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.at_accepts hne)
    · (focus
         ((first
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqSelf ?_
             | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipLast ?_);
           repeat
             with_unfolding_none
               first
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.seqAssoc ?_
               | refine _root_.ThreeSum1960614.Machine.Light.Ends.skipThen ?_)
         refine _root_.ThreeSum1960614.Machine.Light.Ends.setToThen (_root_.ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.index J j r) ?_ ?_ ?_
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

theorem solution : type_of% (@ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.meets__implementation_44279ce992) := (@ThreeSum1960614.Machine.ThreeSum1960614.LightQuarticSwitch.meets__implementation_44279ce992)

#print axioms solution
